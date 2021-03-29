#![allow(dead_code)]

use std::convert::TryFrom;

use tendermint_rpc as rpc;

use tendermint_light_client::{
    components::{self, io::AtHeight},
    light_client::{LightClient as TMLightClient, Options as TMOptions},
    operations,
    state::State as ClientState,
    store::{memory::MemoryStore, LightStore},
    types::Height as TMHeight,
    types::{LightBlock, Status},
};

use ibc::ics24_host::identifier::ChainId;

use crate::{
    chain::CosmosSdkChain,
    config::ChainConfig,
    error::{self, Error},
};

pub struct LightClient {
    chain_id: ChainId,
    client: TMLightClient,
    io: Box<dyn components::io::Io>,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn verify_to_latest(&mut self, trusted: ibc::Height) -> Result<LightBlock, Error> {
        let mut state = self.prepare_state(trusted)?;

        let light_block = self
            .client
            .verify_to_highest(&mut state)
            .map_err(|e| error::Kind::LightClient(self.chain_id.to_string()).context(e))?;

        Ok(light_block)
    }

    fn verify_to_target(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
    ) -> Result<LightBlock, Error> {
        let target_height = TMHeight::try_from(target.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        let mut state = self.prepare_state(trusted)?;

        let light_block = self
            .client
            .verify_to_target(target_height, &mut state)
            .map_err(|e| error::Kind::LightClient(self.chain_id.to_string()).context(e))?;

        Ok(light_block)
    }
}

impl LightClient {
    pub fn from_config(config: &ChainConfig) -> Result<Self, Error> {
        let options = TMOptions {
            trust_threshold: config.trust_threshold,
            trusting_period: config.trusting_period,
            clock_drift: config.clock_drift,
        };

        let rpc_client = rpc::HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| error::Kind::LightClient(config.rpc_addr.to_string()).context(e))?;

        let peer = config.primary().ok_or_else(|| {
            error::Kind::LightClient(config.rpc_addr.to_string()).context("no primary peer")
        })?;

        let io = components::io::ProdIo::new(peer.peer_id, rpc_client, Some(peer.timeout));
        let hasher = operations::hasher::ProdHasher;
        let clock = components::clock::SystemClock;
        let verifier = components::verifier::ProdVerifier::default();
        let scheduler = components::scheduler::basic_bisecting_schedule;

        let client = TMLightClient::new(
            peer.peer_id,
            options,
            clock,
            scheduler,
            verifier,
            hasher,
            io.clone(),
        );

        Ok(Self {
            chain_id: config.id.clone(),
            client,
            io: Box::new(io),
        })
    }

    fn prepare_state(&self, trusted: ibc::Height) -> Result<ClientState, Error> {
        let trusted_height = TMHeight::try_from(trusted.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        let trusted_block = self.fetch_light_block(AtHeight::At(trusted_height))?;

        let mut store = MemoryStore::new();
        store.insert(trusted_block, Status::Trusted);

        Ok(ClientState::new(store))
    }

    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, Error> {
        self.io.fetch_light_block(height).map_err(|e| {
            error::Kind::LightClient(self.chain_id.to_string())
                .context(e)
                .into()
        })
    }
}
