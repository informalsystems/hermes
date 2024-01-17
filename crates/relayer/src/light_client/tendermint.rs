mod detector;

use std::time::Duration;

#[cfg(test)]
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::{
    clients::ics07_tendermint::{
        header::Header as TmHeader,
        misbehaviour::Misbehaviour as TmMisbehaviour,
    },
    core::{
        ics02_client::{
            events::UpdateClient,
            header::AnyHeader,
        },
        ics24_host::identifier::ChainId,
    },
    Height as ICSHeight,
};
use itertools::Itertools;
use tendermint::Time;
use tendermint_light_client::{
    components::{
        self,
        io::{
            AtHeight,
            Io,
            ProdIo,
        },
    },
    light_client::LightClient as TmLightClient,
    state::State as LightClientState,
    store::{
        memory::MemoryStore,
        LightStore,
    },
    verifier::{
        types::{
            Height as TMHeight,
            LightBlock,
            PeerId,
            Status,
        },
        ProdVerifier,
    },
};
use tendermint_light_client_detector::Divergence;
use tendermint_rpc as rpc;
use tracing::{
    debug,
    error,
    trace,
    warn,
};

use super::{
    io::{
        AnyIo,
        RestartAwareIo,
    },
    Verified,
};
use crate::{
    chain::cosmos::{
        config::CosmosSdkConfig,
        CosmosSdkChain,
    },
    client_state::AnyClientState,
    error::Error,
    misbehaviour::{
        AnyMisbehaviour,
        MisbehaviourEvidence,
    },
};

pub struct LightClient {
    chain_id: ChainId,
    peer_id: PeerId,
    io: AnyIo,
    enable_verification: bool,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn header_and_minimal_set(
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
        now: Time,
    ) -> Result<Verified<TmHeader>, Error> {
        let Verified { target, supporting } =
            self.verify(trusted_height, target_height, client_state, now)?;

        // Omit the trusted header from the minimal supporting set, as it is not
        // needed when submitting the update client message.
        let supporting = {
            let trusted_height = TMHeight::from(trusted_height);

            supporting
                .into_iter()
                .filter(|lb| lb.height() != trusted_height)
                .collect()
        };

        let (target, supporting) = self.adjust_headers(trusted_height, target, supporting)?;

        Ok(Verified { target, supporting })
    }

    fn verify(
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
        now: Time,
    ) -> Result<Verified<LightBlock>, Error> {
        trace!(%trusted_height, %target_height, "light client verification");

        if !self.enable_verification {
            let target = self.fetch(target_height)?;

            return Ok(Verified {
                target,
                supporting: vec![],
            });
        }

        let client = self.prepare_client(client_state, now)?;
        let mut state = self.prepare_state(trusted_height)?;

        // Verify the target header
        let target = client
            .verify_to_target(target_height.into(), &mut state)
            .map_err(|e| Error::light_client_verification(self.chain_id.to_string(), e))?;

        // Collect the verification trace for the target block
        let target_trace = state.get_trace(target.height());

        // Compute the supporting set, sorted by ascending height, omitting the target header
        let supporting = target_trace
            .into_iter()
            .unique_by(LightBlock::height)
            .sorted_by_key(LightBlock::height)
            .filter(|lb| lb.height() != target.height())
            .collect_vec();

        Ok(Verified { target, supporting })
    }

    fn fetch(&mut self, height: ICSHeight) -> Result<LightBlock, Error> {
        trace!(%height, "fetching header");

        self.fetch_light_block(AtHeight::At(height.into()))
    }

    /// Perform misbehavior detection on the given client state and update client event.
    fn detect_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
        now: Time,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        crate::time!(
            "light client check_misbehaviour",
            {
                "src_chain": self.chain_id,
            }
        );

        let any_header = update.header.as_ref().ok_or_else(|| {
            Error::misbehaviour(format!(
                "missing header in update client event {}",
                self.chain_id
            ))
        })?;

        let update_header: &TmHeader = match any_header {
            AnyHeader::Tendermint(header) => Ok(header),
        }?;

        let client_state = match client_state {
            AnyClientState::Tendermint(client_state) => Ok(client_state),

            #[cfg(test)]
            _ => Err(Error::misbehaviour(format!(
                "client type incompatible for chain {}",
                self.chain_id
            ))),
        }?;

        let next_validators = self
            .io
            .fetch_validator_set(
                AtHeight::At(update_header.signed_header.header.height.increment()),
                Some(update_header.signed_header.header.proposer_address),
            )
            .map_err(|e| Error::light_client_io(self.chain_id.to_string(), e))?;

        let target_block: LightBlock = LightBlock {
            signed_header: update_header.signed_header.clone(),
            validators: update_header.validator_set.clone(),
            next_validators,
            provider: self.peer_id,
        };

        let trusted_block = self.fetch(update_header.trusted_height)?;
        if trusted_block.validators.hash() != update_header.trusted_validator_set.hash() {
            return Err(Error::misbehaviour(format!(
                "mismatch between the trusted validator set of the update \
                header ({}) and that of the trusted block that was fetched ({}), \
                aborting misbehaviour detection.",
                trusted_block.validators.hash(),
                update_header.trusted_validator_set.hash()
            )));
        }

        let divergence = detector::detect(
            self.peer_id,
            self.io.rpc_client().clone(),
            target_block,
            trusted_block,
            client_state,
            now,
        );

        match divergence {
            Ok(None) => {
                debug!("no misbehavior detected");
                Ok(None)
            }
            Ok(Some(Divergence {
                evidence,
                challenging_block,
            })) => {
                warn!("misbehavior detected, reporting evidence to RPC witness node and primary chain");
                debug!("evidence: {evidence:#?}");
                debug!("challenging block: {challenging_block:#?}");

                warn!("waiting 5 seconds before reporting evidence to RPC witness node");
                std::thread::sleep(Duration::from_secs(5));

                match detector::report_evidence(
                    self.io.rpc_client().clone(),
                    evidence.against_primary,
                ) {
                    Ok(hash) => warn!("evidence reported to RPC witness node with hash: {hash}"),
                    Err(e) => error!("failed to report evidence to RPC witness node: {e}"),
                }

                let target_block = self.fetch(update_header.height())?;
                let trusted_height = TMHeight::from(update_header.trusted_height);
                let trace = evidence
                    .witness_trace
                    .into_vec()
                    .into_iter()
                    .filter(|lb| {
                        lb.height() != target_block.height() && lb.height() != trusted_height
                    })
                    .collect();

                let (target_header, supporting_headers) =
                    self.adjust_headers(update_header.trusted_height, target_block, trace)?;

                let evidence = MisbehaviourEvidence {
                    misbehaviour: AnyMisbehaviour::Tendermint(TmMisbehaviour {
                        client_id: update.client_id().clone(),
                        header1: update_header.clone(),
                        header2: TmHeader {
                            signed_header: challenging_block.signed_header,
                            validator_set: challenging_block.validators,
                            trusted_height: target_header.trusted_height,
                            trusted_validator_set: target_header.trusted_validator_set,
                        },
                    }),
                    supporting_headers: supporting_headers
                        .into_iter()
                        .map(AnyHeader::Tendermint)
                        .collect(),
                };

                Ok(Some(evidence))
            }
            Err(e) => {
                error!("could not detect misbehavior: {}", e);
                Err(e)
            }
        }
    }
}

fn io_for_addr(
    addr: &rpc::Url,
    peer_id: PeerId,
    timeout: Option<Duration>,
) -> Result<ProdIo, Error> {
    let rpc_client = rpc::HttpClient::new(addr.clone()).map_err(|e| Error::rpc(addr.clone(), e))?;
    Ok(ProdIo::new(peer_id, rpc_client, timeout))
}

impl LightClient {
    pub fn from_cosmos_sdk_config(
        config: &CosmosSdkConfig,
        peer_id: PeerId,
    ) -> Result<Self, Error> {
        let live_io = io_for_addr(&config.rpc_addr, peer_id, Some(config.rpc_timeout))?;

        let io = match &config.genesis_restart {
            None => AnyIo::Prod(live_io),
            Some(genesis_restart) => {
                let archive_io = io_for_addr(
                    &genesis_restart.archive_addr,
                    peer_id,
                    Some(config.rpc_timeout),
                )?;

                AnyIo::RestartAware(RestartAwareIo::new(
                    genesis_restart.restart_height,
                    live_io,
                    archive_io,
                ))
            }
        };

        // If the full node is configured as trusted then, in addition to headers not being verified,
        // the verification traces will not be provided. This may cause failure in client
        // updates after significant change in validator sets.
        let enable_verification = !config.trusted_node;

        Ok(Self {
            chain_id: config.id.clone(),
            peer_id,
            io,

            enable_verification,
        })
    }

    fn prepare_client(
        &self,
        client_state: &AnyClientState,
        now: Time,
    ) -> Result<TmLightClient, Error> {
        let clock = components::clock::FixedClock::new(now);
        let verifier = ProdVerifier::default();
        let scheduler = components::scheduler::basic_bisecting_schedule;

        let client_state = match client_state {
            AnyClientState::Tendermint(client_state) => Ok(client_state),

            #[cfg(test)]
            _ => Err(Error::client_type_mismatch(
                ClientType::Tendermint,
                client_state.client_type(),
            )),
        }?;

        Ok(TmLightClient::new(
            self.peer_id,
            client_state.as_light_client_options(),
            clock,
            scheduler,
            verifier,
            self.io.clone(),
        ))
    }

    fn prepare_state(&self, trusted_height: ICSHeight) -> Result<LightClientState, Error> {
        let trusted_block = self.fetch_light_block(AtHeight::At(trusted_height.into()))?;

        let mut store = MemoryStore::new();
        store.insert(trusted_block, Status::Trusted);

        Ok(LightClientState::new(store))
    }

    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, Error> {
        self.io
            .fetch_light_block(height)
            .map_err(|e| Error::light_client_io(self.chain_id.to_string(), e))
    }

    fn adjust_headers(
        &mut self,
        trusted_height: ICSHeight,
        target: LightBlock,
        supporting: Vec<LightBlock>,
    ) -> Result<(TmHeader, Vec<TmHeader>), Error> {
        use super::LightClient;

        tracing::info!(
            trusted = %trusted_height, target = %target.height(),
            "adjusting headers with {} supporting headers", supporting.len()
        );

        // Get the light block at trusted_height + 1 from chain.
        //
        // NOTE: This is needed to get the next validator set. While there is a next validator set
        //       in the light block at trusted height, the proposer is not known/set in this set.
        let trusted_validator_set = self.fetch(trusted_height.increment())?.validators;

        let mut supporting_headers = Vec::with_capacity(supporting.len());

        let mut current_trusted_height = trusted_height;
        let mut current_trusted_validators = trusted_validator_set.clone();

        for support in supporting {
            let header = TmHeader {
                signed_header: support.signed_header.clone(),
                validator_set: support.validators,
                trusted_height: current_trusted_height,
                trusted_validator_set: current_trusted_validators,
            };

            // This header is now considered to be the currently trusted header
            current_trusted_height = header.height();

            // Therefore we can now trust the next validator set, see NOTE above.
            current_trusted_validators = self.fetch(header.height().increment())?.validators;

            supporting_headers.push(header);
        }

        // a) Set the trusted height of the target header to the height of the previous
        // supporting header if any, or to the initial trusting height otherwise.
        //
        // b) Set the trusted validators of the target header to the validators of the successor to
        // the last supporting header if any, or to the initial trusted validators otherwise.
        let (latest_trusted_height, latest_trusted_validator_set) = match supporting_headers.last()
        {
            Some(prev_header) => {
                let prev_succ = self.fetch(prev_header.height().increment())?;
                (prev_header.height(), prev_succ.validators)
            }
            None => (trusted_height, trusted_validator_set),
        };

        let target_header = TmHeader {
            signed_header: target.signed_header,
            validator_set: target.validators,
            trusted_height: latest_trusted_height,
            trusted_validator_set: latest_trusted_validator_set,
        };

        Ok((target_header, supporting_headers))
    }
}
