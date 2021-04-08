use std::convert::TryFrom;

use tendermint_light_client::{
    components::{self, io::AtHeight},
    light_client::{LightClient as TmLightClient, Options as TmOptions},
    operations,
    state::State as LightClientState,
    store::{memory::MemoryStore, LightStore},
    types::Height as TMHeight,
    types::{LightBlock, PeerId, Status},
};
use tendermint_rpc as rpc;

use ibc::{
    downcast,
    ics02_client::{
        client_misbehaviour::{AnyMisbehaviour, Misbehaviour},
        client_state::AnyClientState,
        client_type::ClientType,
        events::UpdateClient,
        header::AnyHeader,
    },
    ics07_tendermint::{header::Header as TmHeader, misbehaviour::Misbehaviour as TmMisbehaviour},
    ics24_host::identifier::ChainId,
};

use crate::error::Kind;
use crate::{
    chain::CosmosSdkChain,
    config::ChainConfig,
    error::{self, Error},
};

pub struct LightClient {
    chain_id: ChainId,
    peer_id: PeerId,
    io: components::io::ProdIo,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn verify(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<LightBlock, Error> {
        let target_height = TMHeight::try_from(target.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        let client = self.prepare_client(client_state)?;
        let mut state = self.prepare_state(trusted)?;

        let light_block = client
            .verify_to_target(target_height, &mut state)
            .map_err(|e| error::Kind::LightClient(self.chain_id.to_string()).context(e))?;

        Ok(light_block)
    }

    fn fetch(&mut self, height: ibc::Height) -> Result<LightBlock, Error> {
        let height = TMHeight::try_from(height.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        self.fetch_light_block(AtHeight::At(height))
    }

    fn build_misbehaviour(
        &mut self,
        client_state: &AnyClientState,
        update: UpdateClient,
        latest_chain_height: ibc::Height,
    ) -> Result<Option<AnyMisbehaviour>, Error> {
        crate::time!("light client build_misbehaviour");

        let update_header = update.header.clone().ok_or_else(|| {
            Kind::Misbehaviour(format!(
                "missing header in update client event {}",
                self.chain_id
            ))
        })?;
        let tm_ibc_client_header =
            downcast!(update_header => AnyHeader::Tendermint).ok_or_else(|| {
                Kind::Misbehaviour(format!(
                    "header type incompatible for chain {}",
                    self.chain_id
                ))
            })?;

        // set the target height to the minimum between the update height and latest chain height
        let target_height = std::cmp::min(*update.consensus_height(), latest_chain_height);
        let trusted_height = tm_ibc_client_header.trusted_height;
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

        let tm_witness_node_header = {
            let trusted_light_block = self.fetch(trusted_height.increment())?;
            let target_light_block = self.verify(trusted_height, target_height, &client_state)?;
            TmHeader {
                trusted_height,
                signed_header: target_light_block.signed_header.clone(),
                validator_set: target_light_block.validators,
                trusted_validator_set: trusted_light_block.validators,
            }
        };

        let misbehaviour = if tm_witness_node_header.incompatible_with(&tm_ibc_client_header) {
            Some(
                AnyMisbehaviour::Tendermint(TmMisbehaviour {
                    client_id: update.client_id().clone(),
                    header1: tm_ibc_client_header,
                    header2: tm_witness_node_header,
                })
                .wrap_any(),
            )
        } else {
            None
        };

        Ok(misbehaviour)
    }
}

impl LightClient {
    pub fn from_config(config: &ChainConfig, peer_id: PeerId) -> Result<Self, Error> {
        let rpc_client = rpc::HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| error::Kind::LightClient(config.rpc_addr.to_string()).context(e))?;

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
        let verifier = components::verifier::ProdVerifier::default();
        let scheduler = components::scheduler::basic_bisecting_schedule;

        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                error::Kind::ClientTypeMismatch {
                    expected: ClientType::Tendermint,
                    got: client_state.client_type(),
                }
            })?;

        let params = TmOptions {
            trust_threshold: client_state.trust_level,
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
        let trusted_height = TMHeight::try_from(trusted.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        let trusted_block = self.fetch_light_block(AtHeight::At(trusted_height))?;

        let mut store = MemoryStore::new();
        store.insert(trusted_block, Status::Trusted);

        Ok(LightClientState::new(store))
    }

    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, Error> {
        use tendermint_light_client::components::io::Io;

        self.io.fetch_light_block(height).map_err(|e| {
            error::Kind::LightClient(self.chain_id.to_string())
                .context(e)
                .into()
        })
    }
}
