use std::convert::TryFrom;

use tendermint_light_client::{
    builder::LightClientBuilder, builder::SupervisorBuilder, light_client, store, supervisor,
    supervisor::Handle, supervisor::Supervisor, types::Height as TMHeight, types::LightBlock,
};
use tendermint_rpc as rpc;

use crate::{
    chain::CosmosSdkChain,
    config::{ChainConfig, LightClientConfig, StoreConfig},
    error,
};
use ibc::ics24_host::identifier::ChainId;

pub struct LightClient {
    handle: Box<dyn Handle>,
    chain_id: ChainId,
}

impl super::LightClient<CosmosSdkChain> for LightClient {
    fn latest_trusted(&self) -> Result<Option<LightBlock>, error::Error> {
        self.handle.latest_trusted().map_err(|e| {
            error::Kind::LightClientSupervisor(self.chain_id.clone())
                .context(e)
                .into()
        })
    }

    fn verify_to_latest(&self) -> Result<LightBlock, error::Error> {
        self.handle.verify_to_highest().map_err(|e| {
            error::Kind::LightClientSupervisor(self.chain_id.clone())
                .context(e)
                .into()
        })
    }

    fn verify_to_target(&self, height: ibc::Height) -> Result<LightBlock, error::Error> {
        let height = TMHeight::try_from(height.revision_height)
            .map_err(|e| error::Kind::InvalidHeight.context(e))?;

        self.handle.verify_to_target(height).map_err(|e| {
            error::Kind::LightClientSupervisor(self.chain_id.clone())
                .context(e)
                .into()
        })
    }

    fn get_minimal_set(
        &self,
        _latest_client_state_height: ibc::Height,
        _target_height: ibc::Height,
    ) -> Result<Vec<ibc::Height>, error::Error> {
        todo!()
    }
}

impl LightClient {
    fn new(handle: impl Handle + 'static, chain_id: ChainId) -> Self {
        Self {
            handle: Box::new(handle),
            chain_id,
        }
    }

    pub fn from_config(
        chain_config: &ChainConfig,
        reset: bool,
    ) -> Result<(Self, Supervisor), error::Error> {
        let supervisor = build_supervisor(&chain_config, reset)?;
        let handle = supervisor.handle();

        Ok((Self::new(handle, chain_config.id.clone()), supervisor))
    }
}

fn build_instance(
    config: &LightClientConfig,
    options: light_client::Options,
    reset: bool,
) -> Result<supervisor::Instance, error::Error> {
    let rpc_client = rpc::HttpClient::new(config.address.clone())
        .map_err(|e| error::Kind::LightClientInstance(config.address.to_string()).context(e))?;

    let store: Box<dyn store::LightStore> = match &config.store {
        StoreConfig::Disk { path } => {
            let db = sled::open(path).map_err(|e| {
                error::Kind::LightClientInstance(config.address.to_string()).context(e)
            })?;
            Box::new(store::sled::SledStore::new(db))
        }
        StoreConfig::Memory { .. } => Box::new(store::memory::MemoryStore::new()),
    };

    let builder = LightClientBuilder::prod(
        config.peer_id,
        rpc_client,
        store,
        options,
        Some(config.timeout),
    );

    let builder = if reset {
        builder.trust_primary_at(config.trusted_height, config.trusted_header_hash)
    } else {
        builder.trust_from_store()
    }
    .map_err(|e| error::Kind::LightClientInstance(config.address.to_string()).context(e))?;

    Ok(builder.build())
}

fn build_supervisor(config: &ChainConfig, reset: bool) -> Result<Supervisor, error::Error> {
    let options = light_client::Options {
        trust_threshold: config.trust_threshold,
        trusting_period: config.trusting_period,
        clock_drift: config.clock_drift,
    };

    let primary_config = config.primary().ok_or_else(|| {
        error::Kind::LightClientSupervisor(config.id.clone())
            .context("missing light client primary peer config")
    })?;

    let witnesses_configs = config.witnesses().ok_or_else(|| {
        error::Kind::LightClientSupervisor(config.id.clone())
            .context("missing light client witnesses peer config")
    })?;

    let primary = build_instance(primary_config, options, reset)?;

    let mut witnesses = Vec::with_capacity(witnesses_configs.len());
    for conf in witnesses_configs {
        let instance = build_instance(conf, options, reset)?;
        witnesses.push((conf.peer_id, conf.address.clone(), instance));
    }

    let supervisor = SupervisorBuilder::new()
        .primary(
            primary_config.peer_id,
            primary_config.address.clone(),
            primary,
        )
        .witnesses(witnesses)
        .map_err(|e| error::Kind::LightClientSupervisor(config.id.clone()).context(e))?
        .build_prod();

    Ok(supervisor)
}
