use std::{ops::Deref, time::Duration};

// use crate::application::APPLICATION;

use abscissa_core::{
    application::fatal_error,
    error::BoxError,
    tracing::{debug, info},
    Command, Options, Runnable,
};

use client::LightClient;
use futures::Future;
use tendermint::chain;
use tendermint_light_client::{
    builder::{LightClientBuilder, SupervisorBuilder},
    light_client, store,
    supervisor::{self, Supervisor},
    types::PeerId,
};

use relayer::{
    chain::{Chain, CosmosSDKChain},
    client,
    client::TrustOptions,
    config::Config,
};

use crate::{
    commands::utils::block_on,
    light::config::{LightConfig, LIGHT_CONFIG_PATH},
    prelude::*,
};

#[derive(Command, Debug, Options)]
pub struct StartCmd {
    #[options(help = "reset state from trust options", short = "r")]
    reset: bool,
}

impl StartCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        let light_config = LightConfig::load(LIGHT_CONFIG_PATH)?;

        // FIXME: This just hangs and never runs the given future
        // abscissa_tokio::run(&APPLICATION, ...).unwrap();

        debug!("launching 'start' command");
        // if !config.local_chains.is_empty() {
        //     debug!(
        //         "found the following local chains: {:?}",
        //         config.local_chains
        //     );
        // }

        // Spawn all tasks on the same thread that calls `block_on`, ie. the main thread.
        // This allows us to spawn tasks which do not implement `Send`,
        // like the light client task.
        let local = tokio::task::LocalSet::new();

        block_on(local.run_until(self.task(config, light_config)))?;

        Ok(())
    }

    async fn task(&self, config: Config, light_config: LightConfig) -> Result<(), BoxError> {
        let mut chains: Vec<CosmosSDKChain> = vec![];

        for chain_config in &config.chains {
            let light_config = light_config.for_chain(&chain_config.id).ok_or_else(|| {
                format!(
                    "could not find light client configuration for chain {}",
                    chain_config.id
                )
            })?;

            info!(chain.id = %chain_config.id, "spawning light client");

            let mut chain = CosmosSDKChain::from_config(chain_config.clone())?;
            let task = create_client_task(&mut chain, light_config.clone(), self.reset).await?;

            chains.push(chain);
            tokio::task::spawn_local(task);
        }

        relayer_task(&config, chains).await?;

        Ok(())
    }
}

impl Runnable for StartCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

async fn relayer_task(config: &Config, chains: Vec<CosmosSDKChain>) -> Result<(), BoxError> {
    for chain in &chains {
        let light_client = chain.light_client().ok_or_else(|| {
            format!(
                "light client for chain {} has not been initialized",
                chain.id()
            )
        })?;

        if let Some(latest_trusted) = light_client.latest_trusted().await? {
            info!(
                chain.id = %chain.id(),
                "latest trusted state is at height {:?}",
                latest_trusted.height(),
            );
        } else {
            warn!(
                chain.id = %chain.id(),
                "no latest trusted state",
            );
        }
    }

    let mut interval = tokio::time::interval(Duration::from_secs(2));

    loop {
        interval.tick().await;
    }
}

async fn create_client_task(
    chain: &mut CosmosSDKChain,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<impl Future<Output = Result<(), BoxError>>, BoxError> {
    status_info!(
        "Relayer",
        "spawning light client for chain {}",
        chain.config().id,
    );

    let supervisor = create_client(chain, trust_options, reset).await?;
    let handle = supervisor.handle();

    let task = client_task(chain.id().clone(), supervisor);

    let light_client = client::tendermint::LightClient::new(handle);
    chain.set_light_client(light_client);

    Ok(task)
}

fn build_instance(
    peer_id: PeerId,
    chain: &CosmosSDKChain,
    store: store::sled::SledStore,
    options: light_client::Options,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<supervisor::Instance, BoxError> {
    let builder = LightClientBuilder::prod(
        peer_id,
        chain.rpc_client().clone(),
        Box::new(store),
        options,
        Some(Duration::from_secs(10)), // TODO: Make configurable
    );

    let builder = if reset {
        info!(chain.id = %chain.id(), "resetting client to trust options state");
        builder.trust_primary_at(trust_options.height, trust_options.header_hash)?
    } else {
        info!(chain.id = %chain.id(), "starting client from stored trusted state");
        builder.trust_from_store()?
    };

    Ok(builder.build())
}

async fn create_client(
    chain: &mut CosmosSDKChain,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<Supervisor, BoxError> {
    let chain_config = chain.config();
    let id = chain_config.id.clone();

    let db_path = format!("store_{}.db", chain.id());
    let store = store::sled::SledStore::new(sled::open(db_path)?);

    // FIXME: Remove or make configurable
    let primary_id: PeerId = "BADFADAD0BEFEEDC0C0ADEADBEEFC0FFEEFACADE".parse().unwrap();
    let witness_id: PeerId = "EFEEDC0C0ADEADBEEFC0FFEEFACADBADFADAD0BE".parse().unwrap();

    let options = light_client::Options {
        trust_threshold: trust_options.trust_threshold,
        trusting_period: trust_options.trusting_period,
        clock_drift: Duration::from_secs(5), // TODO: Make configurable
    };

    let primary = build_instance(
        primary_id,
        &chain,
        store.clone(),
        options,
        trust_options.clone(),
        reset,
    )?;

    let witness = build_instance(witness_id, &chain, store, options, trust_options, reset)?;

    let supervisor = SupervisorBuilder::new()
        .primary(primary_id, chain_config.rpc_addr.clone(), primary)
        .witness(witness_id, chain_config.rpc_addr.clone(), witness)
        .build_prod();

    Ok(supervisor)
}

async fn client_task(chain_id: chain::Id, supervisor: Supervisor) -> Result<(), BoxError> {
    match supervisor.latest_trusted() {
        Some(trusted_state) => {
            info!(
                chain.id = %chain_id,
                "spawned new client now at trusted state: {} at height {}",
                trusted_state.signed_header.header.hash(),
                trusted_state.signed_header.header.height,
            );

            update_client(chain_id, supervisor).await?;
        }
        None => {
            error!(
                chain.id = %chain_id,
                "no initial trusted state, aborting"
            );
        }
    }

    Ok(())
}

async fn update_client(chain_id: chain::Id, mut supervisor: Supervisor) -> Result<(), BoxError> {
    debug!(chain.id = %chain_id, "updating headers");

    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        interval.tick().await;

        info!(chain.id = %chain_id, "updating client");

        // FIXME: This should done via spawn_blocking
        let result = supervisor.verify_to_highest();

        match result {
            Ok(trusted_state) => info!(
                chain.id = %chain_id,
                "client updated to trusted state: {} at height {}",
                trusted_state.signed_header.header.hash(),
                trusted_state.signed_header.header.height
            ),

            Err(err) => error!(chain.id = %chain_id, "error when updating headers: {}", err),
        }
    }
}
