use color_eyre::eyre::Context;
use sqlx::PgPool;
use tendermint_rpc::Url;
use tracing::{error, info};

use crate::{
    error::ReportError,
    event_listener::{EventBatch, EventListener, MonitorCmd},
};

#[tracing::instrument(skip_all)]
pub async fn listen(pool: PgPool, node_addr: Url) -> Result<(), ReportError> {
    let (mut listener, mut rx_batch, tx_cmd) = EventListener::new(node_addr)
        .await
        .wrap_err("failed to start event listner")?;

    listener
        .subscribe()
        .await
        .wrap_err("failed to subscribe to WS events")?;

    tokio::spawn(listener.run());

    while let Some(batch) = rx_batch.recv().await {
        match batch {
            Ok(batch) => process_batch(&pool, batch).await?,
            Err(e) => error!("got error via WebSocket: {}", e),
        }
    }

    info!("Event stream is over");

    tx_cmd
        .send(MonitorCmd::Shutdown)
        .wrap_err("failed to shutdown event listener")?;

    Ok(())
}

#[tracing::instrument(skip_all)]
async fn process_batch(_pool: &PgPool, batch: EventBatch) -> Result<(), ReportError> {
    // TODO: Implement this

    info!("received event batch: {batch:#?}");

    Ok(())
}
