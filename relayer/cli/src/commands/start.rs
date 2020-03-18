use std::future::Future;
use std::time::{Duration, SystemTime};

// use crate::application::APPLICATION;
use crate::prelude::*;

use abscissa_core::tracing::{debug, error, info, warn};
use abscissa_core::{Command, Options, Runnable};

use tendermint::lite::types::Header;

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

        block_on(async {
            for chain_config in config.chains {
                info!(chain.id = %chain_config.id, "spawning light client");

                let _handle = tokio::spawn(async move {
                    let client = create_client(chain_config).await;
                    let trusted_state = client.last_trusted_state().unwrap();

                    info!(
                        chain.id = %client.chain().id(),
                        "Spawned new client now at trusted state: {} at height {}",
                        trusted_state.last_header().header().hash(),
                        trusted_state.last_header().header().height(),
                    );

                    update_headers(client).await;
                });
            }

            start_relayer().await
        })
    }
}

async fn start_relayer() {
    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        info!(target: "relayer_cli::relayer", "Relayer is running");
        interval.tick().await;
    }
}

async fn update_headers<C: Chain, S: Store<C>>(mut client: Client<C, S>) {
    debug!(chain.id = %client.chain().id(), "updating headers");

    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        let result = client.update(SystemTime::now()).await;

        match result {
            Ok(Some(trusted_state)) => info!(
                chain.id = %client.chain().id(),
                "Updated to trusted state: {} at height {}",
                trusted_state.header().hash(),
                trusted_state.header().height()
            ),

            Ok(None) => {
                warn!(chain.id = %client.chain().id(), "Ignoring update to a previous state")
            }
            Err(err) => {
                error!(chain.id = %client.chain().id(), "Error when updating headers: {}", err)
            }
        }

        interval.tick().await;
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

fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
