use std::time::{Duration, SystemTime};

// use crate::application::APPLICATION;
use crate::prelude::*;

use abscissa_core::tracing::{debug, error, info, warn};
use abscissa_core::{Command, Options, Runnable};

use tendermint::lite::types::Header;

use crate::commands::utils::block_on;
use relayer::chain::tendermint::TendermintChain;
use relayer::chain::Chain;
use relayer::client::Client;
use relayer::config::ChainConfig;
use relayer::store::Store;

#[derive(Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = app_config().clone();

        // FIXME: This just hangs and never runs the given future
        // abscissa_tokio::run(&APPLICATION, ...).unwrap();

        debug!("launching 'start' command");

        // Spawn all tasks on the same thread that calls `block_on`, ie. the main thread.
        // This allows us to spawn tasks which do not implement `Send`,
        // like the light client task.
        let local = tokio::task::LocalSet::new();

        block_on(local.run_until(async move {
            for chain_config in config.chains {
                info!(chain.id = %chain_config.id, "spawning light client");
                tokio::task::spawn_local(spawn_client(chain_config));
            }

            info!("starting relayer");
            relayer_task().await
        }));
    }
}

async fn spawn_client(chain_config: ChainConfig) {
    status_info!(
        "Relayer",
        "spawning light client for chain {}",
        chain_config.id
    );

    let client = create_client(chain_config).await;
    tokio::task::spawn_local(client_task(client))
        .await
        .expect("could not spawn client task")
}

async fn client_task(client: Client<TendermintChain, impl Store<TendermintChain>>) {
    let trusted_state = client.last_trusted_state().unwrap();

    status_ok!(
        client.chain().id(),
        "spawned new client now at trusted state: {} at height {}",
        trusted_state.last_header().header().hash(),
        trusted_state.last_header().header().height(),
    );

    update_client(client).await;
}

async fn relayer_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        info!(target: "relayer_cli::relayer", "relayer is running");
        interval.tick().await;
    }
}

async fn update_client<C: Chain, S: Store<C>>(mut client: Client<C, S>) {
    debug!(chain.id = %client.chain().id(), "updating headers");

    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        interval.tick().await;

        info!(chain.id = %client.chain().id(), "updating client");

        let result = client.update(SystemTime::now()).await;

        match result {
            Ok(Some(trusted_state)) => info!(
                chain.id = %client.chain().id(),
                "client updated to trusted state: {} at height {}",
                trusted_state.header().hash(),
                trusted_state.header().height()
            ),

            Ok(None) => {
                warn!(chain.id = %client.chain().id(), "ignoring update to a previous state")
            }
            Err(err) => {
                error!(chain.id = %client.chain().id(), "error when updating headers: {}", err)
            }
        }
    }
}

async fn create_client(
    chain_config: ChainConfig,
) -> Client<TendermintChain, impl Store<TendermintChain>> {
    let chain = TendermintChain::from_config(chain_config).unwrap();

    let store = relayer::store::persistent(format!("store_{}.db", chain.id())).unwrap(); //FIXME: unwrap
    let trust_options = store.get_trust_options().unwrap(); // FIXME: unwrap

    Client::new(chain, store, trust_options).await.unwrap()
}
