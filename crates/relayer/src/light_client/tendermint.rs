use std::str::FromStr;

use itertools::Itertools;

use rpc::Url;
use tendermint_light_client::{
    components::{
        self,
        io::{AtHeight, Io},
    },
    light_client::LightClient as TmLightClient,
    state::State as LightClientState,
    store::{memory::MemoryStore, LightStore},
};
use tendermint_light_client_verifier::options::Options as TmOptions;
use tendermint_light_client_verifier::types::{Height as TMHeight, LightBlock, PeerId, Status};
use tendermint_light_client_verifier::ProdVerifier;
use tendermint_rpc as rpc;

use ibc_relayer_types::{
    clients::ics07_tendermint::{
        header::{headers_compatible, Header as TmHeader},
        misbehaviour::Misbehaviour as TmMisbehaviour,
    },
    core::{
        ics02_client::{
            client_type::ClientType, events::UpdateClient, header::downcast_header, height::Height,
        },
        ics24_host::identifier::ChainId,
    },
    downcast, Height as ICSHeight,
};
use tracing::trace;

use crate::{
    chain::cosmos::CosmosSdkChain, client_state::AnyClientState, config::ChainConfig, error::Error,
    misbehaviour::MisbehaviourEvidence,
};

use super::Verified;

pub struct LightClient {
    chain_id: ChainId,
    peer_id: PeerId,
    io: components::io::ProdIo,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn header_and_minimal_set(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
        archive_addr: Option<String>,
        halted_height: Option<Height>,
    ) -> Result<Verified<TmHeader>, Error> {
        let Verified { target, supporting } = self.verify(
            trusted,
            target,
            client_state,
            archive_addr.clone(),
            halted_height,
        )?;
        let (target, supporting) =
            self.adjust_headers(trusted, target, supporting, archive_addr)?;
        Ok(Verified { target, supporting })
    }

    fn verify(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
        archive_addr: Option<String>,
        halted_height: Option<ICSHeight>,
    ) -> Result<Verified<LightBlock>, Error> {
        trace!(%trusted, %target, "light client verification");

        let target_height =
            TMHeight::try_from(target.revision_height()).map_err(Error::invalid_height)?;

        // This is for chains which went through a genesis restart without an
        // IBC upgrade proposal.
        // If the update is for a height after the chain went through the restart
        // but uses blocks from before the restart, the address used to update must
        // be the one from the chain configuration.
        let rpc_addr_for_client = if halted_height.map_or(false, |height| target <= height) {
            archive_addr.clone()
        } else {
            None
        };
        let client = self.prepare_client(client_state, rpc_addr_for_client)?;

        // This is for chains which went through a genesis restart without an
        // IBC upgrade proposal.
        // If a halted height was given and the trusted height is lower or equal,
        // the state must be built using a Node containing blocks from before the
        // restart
        let rpc_addr_for_state = if halted_height.map_or(false, |height| trusted <= height) {
            archive_addr
        } else {
            None
        };
        let mut state = self.prepare_state(trusted, rpc_addr_for_state)?;

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

    fn fetch(
        &mut self,
        height: ICSHeight,
        archive_addr: Option<String>,
    ) -> Result<LightBlock, Error> {
        trace!(%height, "fetching header");

        let height = TMHeight::try_from(height.revision_height()).map_err(Error::invalid_height)?;

        self.fetch_light_block(AtHeight::At(height), archive_addr)
    }

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    ///
    /// ## TODO
    /// - [ ] Return intermediate headers as well
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        crate::time!("light client check_misbehaviour");

        let update_header = update.header.clone().ok_or_else(|| {
            Error::misbehaviour(format!(
                "missing header in update client event {}",
                self.chain_id
            ))
        })?;

        let update_header: &TmHeader =
            downcast_header(update_header.as_ref()).ok_or_else(|| {
                Error::misbehaviour(format!(
                    "header type incompatible for chain {}",
                    self.chain_id
                ))
            })?;

        let latest_chain_block = self.fetch_light_block(AtHeight::Highest, None)?;
        let latest_chain_height =
            ICSHeight::new(self.chain_id.version(), latest_chain_block.height().into())
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
            self.verify(trusted_height, target_height, client_state, None, None)?;

        if !headers_compatible(&target.signed_header, &update_header.signed_header) {
            let (witness, supporting) =
                self.adjust_headers(trusted_height, target, supporting, None)?;

            let misbehaviour = TmMisbehaviour {
                client_id: update.client_id().clone(),
                header1: update_header.clone(),
                header2: witness,
            }
            .into();

            Ok(Some(MisbehaviourEvidence {
                misbehaviour,
                supporting_headers: supporting.into_iter().map(Into::into).collect(),
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

    fn prepare_client(
        &self,
        client_state: &AnyClientState,
        archive_addr: Option<String>,
    ) -> Result<TmLightClient, Error> {
        let clock = components::clock::SystemClock;
        let verifier = ProdVerifier::default();
        let scheduler = components::scheduler::basic_bisecting_schedule;

        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Error::client_type_mismatch(ClientType::Tendermint, client_state.client_type())
            })?;

        let params = TmOptions {
            trust_threshold: client_state
                .trust_threshold
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
            self.prepare_io(archive_addr)?,
        ))
    }

    fn prepare_state(
        &self,
        trusted: ICSHeight,
        archive_address: Option<String>,
    ) -> Result<LightClientState, Error> {
        let trusted_height =
            TMHeight::try_from(trusted.revision_height()).map_err(Error::invalid_height)?;

        let trusted_block =
            self.fetch_light_block(AtHeight::At(trusted_height), archive_address)?;

        let mut store = MemoryStore::new();
        store.insert(trusted_block, Status::Trusted);

        Ok(LightClientState::new(store))
    }

    fn fetch_light_block(
        &self,
        height: AtHeight,
        archive_addr: Option<String>,
    ) -> Result<LightBlock, Error> {
        self.prepare_io(archive_addr)?
            .fetch_light_block(height)
            .map_err(|e| Error::light_client_io(self.chain_id.to_string(), e))
    }

    fn prepare_io(&self, archive_addr: Option<String>) -> Result<components::io::ProdIo, Error> {
        if let Some(archive_addr) = archive_addr {
            let archive_url = Url::from_str(&archive_addr)
                .map_err(|e| Error::invalid_archive_address(archive_addr, e))?;

            let rpc_client = rpc::HttpClient::new(archive_url.clone())
                .map_err(|e| Error::rpc(archive_url, e))?;

            Ok(components::io::ProdIo::new(self.peer_id, rpc_client, None))
        } else {
            Ok(self.io.clone())
        }
    }

    fn adjust_headers(
        &mut self,
        trusted_height: ICSHeight,
        target: LightBlock,
        supporting: Vec<LightBlock>,
        archive_addr: Option<String>,
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
        let trusted_validator_set = self
            .fetch(trusted_height.increment(), archive_addr.clone())?
            .validators;

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
            current_trusted_validators = self
                .fetch(header.height().increment(), archive_addr.clone())?
                .validators;

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
                let prev_succ = self.fetch(prev_header.height().increment(), archive_addr)?;
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
