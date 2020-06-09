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
use relayer::event_handler::*;
use relayer::event_monitor::*;

use relayer::store::Store;
use std::process;
use tokio::sync::mpsc::{channel, Receiver, Sender};

use ::tendermint::chain::Id as ChainId;
use futures::future::join_all;
use relayer_modules::events::IBCEvent;

#[derive(Command, Debug, Options)]
pub struct StartCmd {
    #[options(help = "reset state from trust options", short = "r")]
    reset: bool,
}

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
            for chain_config in &config.chains {
                info!(chain.id = %chain_config.id, "spawning light client");
                tokio::task::spawn_local(spawn_client(chain_config.clone(), self.reset));
            }

            let (tx, rx) = channel(100);
            let mut all_futures = Vec::new();
            for chain_config in &config.chains {
                info!(chain.id = % chain_config.id, "spawning event monitor for");
                let mut event_monitor = init_monitor(chain_config.clone(), tx.clone()).await;
                let m_handle = tokio::spawn(async move { event_monitor.run().await });
                all_futures.push(m_handle);
            }

            info!("spawning main event handler");
            let mut event_handler = init_event_handler(rx).await;
            let r_handle = tokio::spawn(async move { event_handler.run().await });

            all_futures.push(r_handle);
            let _res = join_all(all_futures).await;
        }))
    }
}

async fn init_monitor(
    chain_config: ChainConfig,
    tx: Sender<(ChainId, Vec<IBCEvent>)>,
) -> EventMonitor {
    EventMonitor::create(chain_config.id, chain_config.rpc_addr.clone(), tx)
        .await
        .unwrap_or_else(|e| {
            status_err!("couldn't initialize event monitor: {}", e);
            process::exit(1);
        })
}

async fn init_event_handler(rx: Receiver<(ChainId, Vec<IBCEvent>)>) -> EventHandler {
    EventHandler::new(rx)
}

async fn spawn_client(chain_config: ChainConfig, reset: bool) {
    status_info!(
        "Relayer",
        "spawning light client for chain {}",
        chain_config.id,
    );

    let client = create_client(chain_config, reset).await;
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

//async fn relayer_task(config: Config) {
//    let mut interval = tokio::time::interval(config.global.timeout);
//
//    loop {
//        info!(target: "relayer_cli::relayer", "relayer is running");
//        interval.tick().await;
//    }
//}

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
    reset: bool,
) -> Client<TendermintChain, impl Store<TendermintChain>> {
    let id = chain_config.id;
    let chain = TendermintChain::from_config(chain_config).unwrap();

    let store = relayer::store::persistent(format!("store_{}.db", chain.id())).unwrap(); //FIXME: unwrap
    let trust_options = store.get_trust_options().unwrap(); // FIXME: unwrap

    if reset {
        info!(chain.id = %id, "resetting client to trust options state");
        let client = Client::new_from_trust_options(chain, store, &trust_options);
        client.await.unwrap() // FIXME: unwrap
    } else {
        info!(chain.id = %chain.id(), "starting client from stored trusted state");
        let client = Client::new_from_trusted_store(chain, store, &trust_options).unwrap(); // FIXME: unwrap
        if client.last_trusted_state().is_none() {
            error!(chain.id = %id, "cannot find stored trusted state, unable to start client");
        }
        client
    }
}
