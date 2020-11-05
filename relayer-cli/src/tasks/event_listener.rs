//! Task for listening to events with the event monitor

use abscissa_core::{error::BoxError, tracing::info};
use futures::future::join_all;
use tokio::sync::mpsc;

use relayer::config::ChainConfig;
use relayer::event_handler::*;
use relayer::event_monitor::*;

use crate::config::Config;

/// Start the event monitor
pub async fn start(config: &Config, relay: bool) -> Result<(), BoxError> {
    let (tx, rx) = mpsc::channel(100);

    let mut all_futures = Vec::new();
    for chain_config in &config.chains {
        info!(chain.id = %chain_config.id, "spawning event monitor for");
        let mut event_monitor = init_monitor(chain_config.clone(), tx.clone()).await?;
        let handle = tokio::spawn(async move { event_monitor.run().await });
        all_futures.push(handle);
    }

    info!("spawning main event handler");
    let mut event_handler = EventHandler::new(rx, relay);
    let handle = tokio::spawn(async move { event_handler.run().await });
    all_futures.push(handle);

    let _res = join_all(all_futures).await;

    Ok(())
}

async fn init_monitor(
    chain_config: ChainConfig,
    tx: mpsc::Sender<EventBatch>,
) -> Result<EventMonitor, BoxError> {
    let mut event_monitor =
        EventMonitor::create(chain_config.id.into(), chain_config.rpc_addr.clone(), tx)
            .await
            .map_err(|e| format!("couldn't initialize event monitor: {}", e))?;

    event_monitor
        .subscribe()
        .await
        .map_err(|e| format!("couldn't initialize subscriptions: {}", e))?;

    Ok(event_monitor)
}
