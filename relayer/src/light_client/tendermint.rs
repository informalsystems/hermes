use std::convert::TryFrom;

use tendermint_rpc as rpc;

use tendermint_light_client::{
    components::{self, io::AtHeight},
    light_client::{LightClient as TmLightClient, Options as TmOptions},
    operations,
    state::State as LightClientState,
    store::{memory::MemoryStore, LightStore},
    types::Height as TMHeight,
    types::{LightBlock, PeerId, Status},
};

use ibc::{downcast, ics02_client::client_state::AnyClientState};
use ibc::{ics02_client::client_type::ClientType, ics24_host::identifier::ChainId};

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
}

impl LightClient {
    pub fn from_config(config: &ChainConfig) -> Result<Self, Error> {
        let rpc_client = rpc::HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| error::Kind::LightClient(config.rpc_addr.to_string()).context(e))?;

        let peer = config.primary().ok_or_else(|| {
            error::Kind::LightClient(config.rpc_addr.to_string()).context("no primary peer")
        })?;

        let io = components::io::ProdIo::new(peer.peer_id, rpc_client, Some(peer.timeout));

        Ok(Self {
            chain_id: config.id.clone(),
            peer_id: peer.peer_id,
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
