use crate::prelude::*;

use abscissa_core::tracing::{debug, info};
use abscissa_core::{Command, Options, Runnable};

use crate::commands::utils::block_on;
use relayer::config::ChainConfig;
use relayer::event_handler::*;
use relayer::event_monitor::*;

use std::process;
use tokio::sync::mpsc::{channel, Sender};

use crate::config::Config;
use ::tendermint::chain::Id as ChainId;
use futures::future::join_all;
use relayer_modules::events::IBCEvent;

#[derive(Command, Debug, Options)]
pub struct ListenCmd {
    //    #[options(help = "reset state from trust options", short = "r")]
//    reset: bool,
}

impl Runnable for ListenCmd {
    fn run(&self) {
        let config = app_config().clone();
        debug!("launching 'listen' command");
        let local = tokio::task::LocalSet::new();

        block_on(local.run_until(async move {
            relayer_task(&config, false).await;
        }))
    }
}

pub async fn relayer_task(config: &Config, relay: bool) {
    let (tx, rx) = channel(100);
    let mut all_futures = Vec::new();
    for chain_config in &config.chains {
        info!(chain.id = % chain_config.id, "spawning event monitor for");
        let mut event_monitor = init_monitor(chain_config.clone(), tx.clone()).await;
        let m_handle = tokio::spawn(async move { event_monitor.run().await });
        all_futures.push(m_handle);
    }

    info!("spawning main event handler");
    let mut event_handler = EventHandler::new(rx, relay);
    let r_handle = tokio::spawn(async move { event_handler.run().await });

    all_futures.push(r_handle);
    let _res = join_all(all_futures).await;
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
