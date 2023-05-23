use alloc::sync::Arc;

use crossbeam_channel as channel;
use futures::stream::StreamExt;
use tokio::task::JoinHandle;
use tokio::{runtime::Runtime as TokioRuntime, sync::mpsc};
use tracing::{debug, error, info, instrument, trace};

use tendermint::abci;
use tendermint_rpc::event::EventData;
use tendermint_rpc::Client;

use tendermint::block::Height as BlockHeight;
use tendermint_rpc::{
    client::CompatMode, event::Event as RpcEvent, SubscriptionClient, WebSocketClient,
    WebSocketClientDriver, WebSocketClientUrl,
};

use ibc_relayer_types::core::ics02_client::events::NewBlock;
use ibc_relayer_types::Height;
use ibc_relayer_types::{core::ics24_host::identifier::ChainId, events::IbcEvent};

use crate::{
    chain::tracking::TrackingId,
    event::{bus::EventBus, error::*, util::dedupe, IbcEventWithHeight},
    telemetry,
    util::retry::{retry_with_index, RetryResult},
};

use super::rpc::extract::extract_events;
use super::{EventBatch, EventSourceCmd, Result, SubscriptionStream, TxEventSourceCmd};

mod retry_strategy {
    use crate::util::retry::clamp_total;
    use core::time::Duration;
    use retry::delay::Fibonacci;

    // Default parameters for the retrying mechanism
    const MAX_DELAY: Duration = Duration::from_secs(60); // 1 minute
    const MAX_TOTAL_DELAY: Duration = Duration::from_secs(10 * 60); // 10 minutes
    const INITIAL_DELAY: Duration = Duration::from_secs(1); // 1 second

    pub fn default() -> impl Iterator<Item = Duration> {
        clamp_total(Fibonacci::from(INITIAL_DELAY), MAX_DELAY, MAX_TOTAL_DELAY)
    }
}

pub struct EventSource {
    chain_id: ChainId,
    /// WebSocket to collect events from
    client: WebSocketClient,
    /// Async task handle for the WebSocket client's driver
    driver_handle: JoinHandle<()>,
    /// Event bus for broadcasting events
    event_bus: EventBus<Arc<Result<EventBatch>>>,
    /// Channel where to receive client driver errors
    rx_err: mpsc::UnboundedReceiver<tendermint_rpc::Error>,
    /// Channel where to send client driver errors
    tx_err: mpsc::UnboundedSender<tendermint_rpc::Error>,
    /// Channel where to receive commands
    rx_cmd: channel::Receiver<EventSourceCmd>,
    /// Node Address
    ws_url: WebSocketClientUrl,
    /// RPC compatibility mode
    rpc_compat: CompatMode,
    /// The subscription for NewBlock events
    subscription: Box<SubscriptionStream>,
    /// Tokio runtime
    rt: Arc<TokioRuntime>,
}

impl EventSource {
    /// Create an event source, and connect to a node
    #[instrument(
        name = "event_source.create",
        level = "error",
        skip_all,
        fields(chain = %chain_id, url = %ws_url)
    )]
    pub fn new(
        chain_id: ChainId,
        ws_url: WebSocketClientUrl,
        rpc_compat: CompatMode,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxEventSourceCmd)> {
        let event_bus = EventBus::new();
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let builder = WebSocketClient::builder(ws_url.clone()).compat_mode(rpc_compat);

        let (client, driver) = rt
            .block_on(builder.build())
            .map_err(|_| Error::client_creation_failed(chain_id.clone(), ws_url.clone()))?;

        let (tx_err, rx_err) = mpsc::unbounded_channel();
        let driver_handle = rt.spawn(run_driver(driver, tx_err.clone()));

        let source = Self {
            rt,
            chain_id,
            client,
            driver_handle,
            event_bus,
            rx_err,
            tx_err,
            rx_cmd,
            ws_url,
            rpc_compat,
            subscription: Box::new(futures::stream::empty()),
        };

        Ok((source, TxEventSourceCmd(tx_cmd)))
    }

    /// Clear the current subscriptions, and subscribe again to all queries.
    #[instrument(name = "event_source.init_subscription", skip_all, fields(chain = %self.chain_id))]
    pub fn init_subscription(&mut self) -> Result<()> {
        let query = super::queries::new_block();
        trace!("subscribing to query: {query}");

        let subscription = self
            .rt
            .block_on(self.client.subscribe(query))
            .map_err(Error::client_subscription_failed)?;

        self.subscription = Box::new(subscription);

        Ok(())
    }

    #[instrument(
        name = "event_source.try_reconnect",
        level = "error",
        skip_all,
        fields(chain = %self.chain_id)
    )]
    fn try_reconnect(&mut self) -> Result<()> {
        trace!("trying to reconnect to WebSocket endpoint {}", self.ws_url);

        // Try to reconnect
        let builder = WebSocketClient::builder(self.ws_url.clone()).compat_mode(self.rpc_compat);

        let (mut client, driver) = self.rt.block_on(builder.build()).map_err(|_| {
            Error::client_creation_failed(self.chain_id.clone(), self.ws_url.clone())
        })?;

        let mut driver_handle = self.rt.spawn(run_driver(driver, self.tx_err.clone()));

        // Swap the new client with the previous one which failed,
        // so that we can shut the latter down gracefully.
        core::mem::swap(&mut self.client, &mut client);
        core::mem::swap(&mut self.driver_handle, &mut driver_handle);

        trace!("reconnected to WebSocket endpoint {}", self.ws_url);

        // Shut down previous client
        trace!("gracefully shutting down previous client",);

        let _ = client.close();

        self.rt
            .block_on(driver_handle)
            .map_err(Error::client_termination_failed)?;

        trace!("previous client successfully shutdown");

        Ok(())
    }

    /// Try to resubscribe to events
    #[instrument(
        name = "event_source.try_resubscribe",
        level = "error",
        skip_all,
        fields(chain = %self.chain_id)
    )]
    fn try_resubscribe(&mut self) -> Result<()> {
        trace!("trying to resubscribe to events");
        self.init_subscription()
    }

    /// Attempt to reconnect the WebSocket client using the given retry strategy.
    ///
    /// See the [`retry`](https://docs.rs/retry) crate and the
    /// [`crate::util::retry`] module for more information.
    #[instrument(
        name = "event_source.reconnect",
        level = "error",
        skip_all,
        fields(chain = %self.chain_id)
    )]
    fn reconnect(&mut self) {
        let result = retry_with_index(retry_strategy::default(), |_| {
            // Try to reconnect
            if let Err(e) = self.try_reconnect() {
                trace!("error when reconnecting: {}", e);
                return RetryResult::Retry(());
            }

            // Try to resubscribe
            if let Err(e) = self.try_resubscribe() {
                trace!("error when resubscribing: {}", e);
                return RetryResult::Retry(());
            }

            RetryResult::Ok(())
        });

        match result {
            Ok(()) => info!(
                "successfully reconnected to WebSocket endpoint {}",
                self.ws_url
            ),
            Err(e) => error!(
                "failed to reconnect to {} after {} retries",
                self.ws_url, e.tries
            ),
        }
    }

    /// Event source loop
    #[allow(clippy::while_let_loop)]
    #[instrument(
        name = "event_source.websocket",
        level = "error",
        skip_all,
        fields(chain = %self.chain_id)
    )]
    pub fn run(mut self) {
        debug!("collecting events");

        // work around double borrow
        let rt = self.rt.clone();

        // Continuously run the event loop, so that when it aborts
        // because of WebSocket client restart, we pick up the work again.
        loop {
            match rt.block_on(self.run_loop()) {
                Next::Continue => continue,
                Next::Abort => break,
                Next::Reconnect => {
                    telemetry!(ws_reconnect, &self.chain_id);
                    self.reconnect();

                    continue;
                }
            }
        }

        debug!("event source is shutting down");

        // Close the WebSocket connection
        let _ = self.client.close();

        // Wait for the WebSocket driver to finish
        let _ = self.rt.block_on(self.driver_handle);

        trace!("event source has successfully shut down");
    }

    async fn run_loop(&mut self) -> Next {
        // Take ownership of the subscriptions
        let mut on_new_block =
            core::mem::replace(&mut self.subscription, Box::new(futures::stream::empty()));

        loop {
            // Process any shutdown or subscription commands
            if let Ok(cmd) = self.rx_cmd.try_recv() {
                match cmd {
                    EventSourceCmd::Shutdown => return Next::Abort,
                    EventSourceCmd::Subscribe(tx) => {
                        if let Err(e) = tx.send(self.event_bus.subscribe()) {
                            error!("failed to send back subscription: {e}");
                        }
                    }
                }
            }

            let result = tokio::select! {
                Some(new_block) = on_new_block.next() => {
                    match new_block {
                        Ok(new_block) => process_new_block(&self.client, &self.chain_id, new_block).await,
                        Err(e) => {
                            error!("failed to receive new block: {}", e);
                            return Next::Reconnect;
                        }
                    }
                }
                Some(e) = self.rx_err.recv() => Err(Error::web_socket_driver(e)),
            };

            // Before handling the batch, check if there are any pending shutdown or subscribe commands.
            if let Ok(cmd) = self.rx_cmd.try_recv() {
                match cmd {
                    EventSourceCmd::Shutdown => return Next::Abort,
                    EventSourceCmd::Subscribe(tx) => {
                        if let Err(e) = tx.send(self.event_bus.subscribe()) {
                            error!("failed to send back subscription: {e}");
                        }
                    }
                }
            }

            match result {
                Ok(None) => continue,
                Ok(Some(batch)) => self.broadcast_batch(batch),
                Err(e) => {
                    if let ErrorDetail::SubscriptionCancelled(reason) = e.detail() {
                        error!("subscription cancelled, reason: {}", reason);

                        self.propagate_error(e);

                        // Reconnect to the WebSocket endpoint, and subscribe again to the queries.
                        return Next::Reconnect;
                    } else {
                        error!("failed to collect events: {}", e);

                        // Reconnect to the WebSocket endpoint, and subscribe again to the queries.
                        return Next::Reconnect;
                    };
                }
            }
        }
    }

    /// Propagate error to subscribers.
    ///
    /// The main use case for propagating RPC errors is for the [`Supervisor`]
    /// to notice that the WebSocket connection or subscription has been closed,
    /// and to trigger a clearing of packets, as this typically means that we have
    /// missed a bunch of events which were emitted after the subscription was closed.
    /// In that case, this error will be handled in [`Supervisor::handle_batch`].
    fn propagate_error(&mut self, error: Error) {
        self.event_bus.broadcast(Arc::new(Err(error)));
    }

    /// Broadcast a batch of events to all subscribers.
    fn broadcast_batch(&mut self, batch: EventBatch) {
        telemetry!(ws_events, &batch.chain_id, batch.events.len() as u64);

        debug!(
            chain = %batch.chain_id,
            count = %batch.events.len(),
            height = %batch.height,
            "broadcasting batch of {} events",
            batch.events.len()
        );

        self.event_bus.broadcast(Arc::new(Ok(batch)));
    }
}

async fn process_new_block(
    client: &WebSocketClient,
    chain_id: &ChainId,
    event: RpcEvent,
) -> Result<Option<EventBatch>> {
    let EventData::NewBlock {
        block,
        result_begin_block: _,
        result_end_block: _,
    } = event.data else { return Ok(None); };

    let Some(block) = block else { return Ok(None); };

    collect_events(client, chain_id, block.header.height).await
}

/// Collect the IBC events from an RPC event
async fn collect_events(
    client: &WebSocketClient,
    chain_id: &ChainId,
    height: BlockHeight,
) -> Result<Option<EventBatch>> {
    let height = Height::from_tm(height, chain_id);

    let abci_events = fetch_all_events(client, height).await?;
    trace!("Found {} ABCI events before dedupe", abci_events.len());

    let abci_events = dedupe(abci_events);
    trace!("Found {} ABCI events after dedupe", abci_events.len());

    let new_block_event =
        IbcEventWithHeight::new(IbcEvent::NewBlock(NewBlock::new(height)), height);

    let mut block_events = extract_events(chain_id, height, &abci_events).unwrap_or_default();
    let mut events = Vec::with_capacity(block_events.len() + 1);
    events.push(new_block_event);
    events.append(&mut block_events);

    trace!(
        "collected {events_len} events at height {height}: {events:#?}",
        events_len = events.len(),
        height = height,
    );

    Ok(Some(EventBatch {
        chain_id: chain_id.clone(),
        tracking_id: TrackingId::new_uuid(),
        height,
        events,
    }))
}

async fn fetch_all_events(client: &WebSocketClient, height: Height) -> Result<Vec<abci::Event>> {
    let height = BlockHeight::try_from(height.revision_height()).unwrap();

    let mut response = client.block_results(height).await.map_err(Error::rpc)?;
    let mut events = vec![];

    if let Some(begin_block_events) = &mut response.begin_block_events {
        events.append(begin_block_events);
    }

    if let Some(txs_results) = &mut response.txs_results {
        for tx_result in txs_results {
            if tx_result.code != abci::Code::Ok {
                // Transaction failed, skip it
                continue;
            }

            events.append(&mut tx_result.events);
        }
    }

    if let Some(end_block_events) = &mut response.end_block_events {
        events.append(end_block_events);
    }

    Ok(events)
}

async fn run_driver(
    driver: WebSocketClientDriver,
    tx: mpsc::UnboundedSender<tendermint_rpc::Error>,
) {
    if let Err(e) = driver.run().await {
        if tx.send(e).is_err() {
            error!("failed to relay driver error to event source");
        }
    }
}

pub enum Next {
    Abort,
    Continue,
    Reconnect,
}
