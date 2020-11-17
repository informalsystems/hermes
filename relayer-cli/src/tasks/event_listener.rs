//! Task for listening to events with the event monitor

use std::{sync::Arc, thread};

use abscissa_core::{error::BoxError, tracing::info};
use crossbeam_channel as channel;

use relayer::config::ChainConfig;
use relayer::event::handler::*;
use relayer::event::monitor::*;

use crate::config::Config;

/// Start the event monitor
pub fn start(
    rt: Arc<tokio::runtime::Runtime>,
    config: &Config,
    relay: bool,
) -> Result<(), BoxError> {
    let (tx, rx) = channel::unbounded();

    for chain_config in &config.chains {
        info!(chain.id = %chain_config.id, "spawning event monitor for");
        let (event_monitor, rx_batch) = init_monitor(chain_config.clone(), rt.clone())?;
        let _ = thread::spawn(|| event_monitor.run());
    }

    info!("running event handler");
    let mut event_handler = EventHandler::new(rx, relay);
    event_handler.run();

    Ok(())
}

fn init_monitor(
    chain_config: ChainConfig,
    rt: Arc<tokio::runtime::Runtime>,
) -> Result<(EventMonitor, channel::Receiver<EventBatch>), BoxError> {
    let (mut event_monitor, rx_batch) =
        EventMonitor::new(chain_config.id, chain_config.rpc_addr, rt)
            .map_err(|e| format!("couldn't initialize event monitor: {}", e))?;

    event_monitor
        .subscribe()
        .map_err(|e| format!("couldn't initialize subscriptions: {}", e))?;

    Ok((event_monitor, rx_batch))
}
