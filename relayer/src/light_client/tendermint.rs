use itertools::Itertools;

use tendermint_light_client::{
    components::{self, io::AtHeight},
    light_client::LightClient as TmLightClient,
    state::State as LightClientState,
    store::{memory::MemoryStore, LightStore},
};
use tendermint_light_client_verifier::operations;
use tendermint_light_client_verifier::options::Options as TmOptions;
use tendermint_light_client_verifier::types::{Height as TMHeight, LightBlock, PeerId, Status};
use tendermint_light_client_verifier::ProdVerifier;
use tendermint_rpc as rpc;

use ibc::{
    clients::ics07_tendermint::{
        header::{headers_compatible, Header as TmHeader},
        misbehaviour::Misbehaviour as TmMisbehaviour,
    },
    core::{
        ics02_client::{
            client_state::AnyClientState,
            client_type::ClientType,
            events::UpdateClient,
            header::{AnyHeader, Header},
            misbehaviour::{Misbehaviour, MisbehaviourEvidence},
        },
        ics24_host::identifier::ChainId,
    },
    downcast,
};
use tracing::trace;

use crate::{chain::cosmos::CosmosSdkChain, config::ChainConfig, error::Error};

use super::Verified;

pub struct LightClient {
    chain_id: ChainId,
    peer_id: PeerId,
    io: components::io::ProdIo,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn header_and_minimal_set(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<TmHeader>, Error> {
        let _span = tracing::span!(
            tracing::Level::DEBUG,
            "header and minimal set",
            trusted = %trusted, target = %target,
            chain = %self.chain_id
        )
        .entered();

        let Verified { target, supporting } = self.verify(trusted, target, client_state)?;

        // let (target, supporting) = self.adjust_headers(trusted, target, supporting)?;

        Ok(Verified { target, supporting })
    }

    fn verify(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<LightBlock>, Error> {
        let _span = tracing::span!(
            tracing::Level::DEBUG,
            "light client verification",
            trusted = %trusted, target = %target,
            chain = %self.chain_id
        )
        .entered();

        let target_height =
            TMHeight::try_from(target.revision_height()).map_err(Error::invalid_height)?;

        let client = self.prepare_client(client_state)?;
        let mut state = self.prepare_state(trusted)?;

        // Verify the target header
        let target = client
            .verify_to_target(target_height, &mut state)
            .map_err(|e| Error::light_client_verification(self.chain_id.to_string(), e))?;

        // Collect the verification trace for the target block
        let target_trace = state.get_trace(target.height());

        // Compute the minimal supporting set, sorted by ascending height
        let supporting = target_trace
            .into_iter()
            .filter(|lb| lb.height() != target.height())
            .unique_by(LightBlock::height)
            .sorted_by_key(LightBlock::height)
            .collect_vec();

        Ok(Verified { target, supporting })
    }

    fn fetch(&mut self, height: ibc::Height) -> Result<LightBlock, Error> {
        trace!(%height, "fetching header");

        let height = TMHeight::try_from(height.revision_height()).map_err(Error::invalid_height)?;

        self.fetch_light_block(AtHeight::At(height))
    }

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    ///
    /// ## TODO
    /// - [ ] Return intermediate headers as well
    fn check_misbehaviour(
        &mut self,
        update: UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        crate::time!("light client check_misbehaviour");

        let update_header = update.header.clone().ok_or_else(|| {
            Error::misbehaviour(format!(
                "missing header in update client event {}",
                self.chain_id
            ))
        })?;

        let update_header = downcast!(update_header => AnyHeader::Tendermint).ok_or_else(|| {
            Error::misbehaviour(format!(
                "header type incompatible for chain {}",
                self.chain_id
            ))
        })?;

        let latest_chain_block = self.fetch_light_block(AtHeight::Highest)?;
        let latest_chain_height =
            ibc::Height::new(self.chain_id.version(), latest_chain_block.height().into())
                .map_err(|_| Error::invalid_height_no_source())?;

        // set the target height to the minimum between the update height and latest chain height
        let target_height = core::cmp::min(update.consensus_height(), latest_chain_height);
        let trusted_height = update_header.trusted_height;

        // TODO - check that a consensus state at trusted_height still exists on-chain,
        // currently we don't have access to Cosmos chain query from here

        if trusted_height >= latest_chain_height {
            // Can happen with multiple FLA attacks, we return no evidence and hope to catch this in
            // the next iteration. e.g:
            // existing consensus states: 1000, 900, 300, 200 (only known by the caller)
            // latest_chain_height = 300
            // target_height = 1000
            // trusted_height = 900
            return Ok(None);
        }

        let Verified { target, supporting } =
            self.verify(trusted_height, target_height, client_state)?;

        if !headers_compatible(&target.signed_header, &update_header.signed_header) {
            let (witness, supporting) = self.adjust_headers(trusted_height, target, supporting)?;

            let misbehaviour = TmMisbehaviour {
                client_id: update.client_id().clone(),
                header1: update_header,
                header2: witness,
            }
            .wrap_any();

            Ok(Some(MisbehaviourEvidence {
                misbehaviour,
                supporting_headers: supporting.into_iter().map(TmHeader::wrap_any).collect(),
            }))
        } else {
            Ok(None)
        }
    }
}

impl LightClient {
    pub fn from_config(config: &ChainConfig, peer_id: PeerId) -> Result<Self, Error> {
        let rpc_client = rpc::HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

        let io = components::io::ProdIo::new(peer_id, rpc_client, Some(config.rpc_timeout));

        Ok(Self {
            chain_id: config.id.clone(),
            peer_id,
            io,
        })
    }

    fn prepare_client(&self, client_state: &AnyClientState) -> Result<TmLightClient, Error> {
        let clock = components::clock::SystemClock;
        let hasher = operations::hasher::ProdHasher;
        let verifier = ProdVerifier::default();
        let scheduler = components::scheduler::basic_bisecting_schedule;

        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Error::client_type_mismatch(ClientType::Tendermint, client_state.client_type())
            })?;

        let params = TmOptions {
            trust_threshold: client_state
                .trust_level
                .try_into()
                .map_err(Error::light_client_state)?,
            trusting_period: client_state.trusting_period,
            clock_drift: client_state.max_clock_drift,
        };

        Ok(TmLightClient::new(
            self.peer_id,
            params,
            clock,
            scheduler,
            verifier,
            hasher,
            self.io.clone(),
        ))
    }

    fn prepare_state(&self, trusted: ibc::Height) -> Result<LightClientState, Error> {
        let trusted_height =
            TMHeight::try_from(trusted.revision_height()).map_err(Error::invalid_height)?;

        let trusted_block = self.fetch_light_block(AtHeight::At(trusted_height))?;

        let mut store = MemoryStore::new();
        store.insert(trusted_block, Status::Trusted);
        tracing::warn!(trusted_height = %trusted, "finished fetching light block & inserted in block store");

        Ok(LightClientState::new(store))
    }

    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, Error> {
        use core::time::Duration;
        use tendermint_light_client::components::io::Io;
        use tracing::warn;

        match height {
            AtHeight::At(fetch_height) => {
                // The height at which Juno-1 halted.
                let juno_client_latest_trusted_height = TMHeight::from(4136530_u32);

                if (fetch_height <= juno_client_latest_trusted_height)
                    && (self.chain_id == ChainId::new("juno".to_owned(), 1))
                {
                    // Create an alternative io for the archive node, to bypass the default full node.
                    warn!("matched on juno-1, below the halt height");

                    let archive_rpc_client =
                        rpc::HttpClient::new("https://rpc-v3-archive.junonetwork.io:443")
                            .expect("could not initialize the rpc client to bypass juno full node");
                    // let peer_id_string = String::from("4b0f1f25d5bff62d6cd674ddbe56df14d58979f3").as_bytes();
                    let dummy_peer_id_u8: [u8; 20] = [0; 20];
                    let peer_id = PeerId::new(dummy_peer_id_u8);
                    // Instantiate a different io targeting the archive node
                    let archive_io = components::io::ProdIo::new(
                        peer_id,
                        archive_rpc_client,
                        Some(Duration::from_secs(20)),
                    );

                    // Fetch the light block from the archive node.
                    return archive_io
                        .fetch_light_block(height)
                        .map_err(|e| Error::light_client_io(self.chain_id.to_string(), e));
                } else {
                    warn!(height = %fetch_height, chain_id = %self.chain_id, "not on juno-1 chain or fetching a different height; using the default io");
                }
            }
            AtHeight::Highest => {
                warn!(
                    "fetching highest height, no need to bypass the default full node; using the default io"
                );
            }
        };

        self.io
            .fetch_light_block(height)
            .map_err(|e| Error::light_client_io(self.chain_id.to_string(), e))
    }

    fn adjust_headers(
        &mut self,
        trusted_height: ibc::Height,
        target: LightBlock,
        supporting: Vec<LightBlock>,
    ) -> Result<(TmHeader, Vec<TmHeader>), Error> {
        use super::LightClient;

        trace!(
            trusted = %trusted_height, target = %target.height(),
            "adjusting headers with {} supporting headers", supporting.len()
        );

        // Get the light block at trusted_height + 1 from chain.
        //
        // NOTE: This is needed to get the next validator set. While there is a next validator set
        //       in the light block at trusted height, the proposer is not known/set in this set.
        trace!(
            height = %trusted_height.increment(),
            "creating trusted validator set"
        );
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

            trace!(
                header = %header.height().increment(),
                "creating supporting headers"
            );
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
