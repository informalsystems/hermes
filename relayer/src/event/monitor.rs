use std::{cmp::Ordering, sync::Arc};

use crossbeam_channel as channel;
use futures::{
    pin_mut,
    stream::{self, select_all, StreamExt},
    Stream,
};
use thiserror::Error;
use tokio::task::JoinHandle;
use tokio::{runtime::Runtime as TokioRuntime, sync::mpsc};
use tracing::{debug, error, info, trace, warn};

use tendermint_rpc::{
    event::Event as RpcEvent,
    query::{EventType, Query},
    Error as RpcError, Result as RpcResult, SubscriptionClient, WebSocketClient,
    WebSocketClientDriver,
};

use ibc::{events::IbcEvent, ics02_client::height::Height, ics24_host::identifier::ChainId};

use crate::util::{
    retry::{retry_count, retry_with_index, RetryResult},
    stream::group_while,
};

mod retry_strategy {
    use crate::util::retry::clamp_total;
    use retry::delay::Fibonacci;
    use std::time::Duration;

    // Default parameters for the retrying mechanism
    const MAX_DELAY: Duration = Duration::from_secs(60); // 1 minute
    const MAX_TOTAL_DELAY: Duration = Duration::from_secs(10 * 60); // 10 minutes
    const INITIAL_DELAY: Duration = Duration::from_secs(1); // 1 second

    pub fn default() -> impl Iterator<Item = Duration> {
        clamp_total(Fibonacci::from(INITIAL_DELAY), MAX_DELAY, MAX_TOTAL_DELAY)
    }
}

#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error("WebSocket driver failed: {0}")]
    WebSocketDriver(RpcError),

    #[error("failed to create WebSocket driver: {0}")]
    ClientCreationFailed(RpcError),

    #[error("failed to terminate previous WebSocket driver: {0}")]
    ClientTerminationFailed(Arc<tokio::task::JoinError>),

    #[error("failed to run previous WebSocket driver to completion: {0}")]
    ClientCompletionFailed(RpcError),

    #[error("failed to subscribe to events via WebSocket client: {0}")]
    ClientSubscriptionFailed(RpcError),

    #[error("failed to collect events over WebSocket subscription: {0}")]
    NextEventBatchFailed(RpcError),

    #[error("failed to extract IBC events: {0}")]
    CollectEventsFailed(String),

    #[error("event monitor failed to dispatch event batch to subscribers")]
    ChannelSendFailed,
}

/// A batch of events from a chain at a specific height
#[derive(Clone, Debug)]
pub struct EventBatch {
    pub chain_id: ChainId,
    pub height: Height,
    pub events: Vec<IbcEvent>,
}

pub trait UnwrapOrClone {
    fn unwrap_or_clone(self: Arc<Self>) -> Self;
}

impl UnwrapOrClone for Result<EventBatch> {
    fn unwrap_or_clone(self: Arc<Self>) -> Self {
        Arc::try_unwrap(self).unwrap_or_else(|batch| batch.as_ref().clone())
    }
}

type SubscriptionResult = RpcResult<RpcEvent>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

pub type Result<T> = std::result::Result<T, Error>;

pub type EventSender = channel::Sender<Result<EventBatch>>;
pub type EventReceiver = channel::Receiver<Result<EventBatch>>;
pub type TxMonitorCmd = channel::Sender<MonitorCmd>;

#[derive(Debug)]
pub enum MonitorCmd {
    Shutdown,
}

/// Connect to a Tendermint node, subscribe to a set of queries,
/// receive push events over a websocket, and filter them for the
/// event handler.
///
/// The default events that are queried are:
/// - [`EventType::NewBlock`]
/// - [`EventType::Tx`]
///
/// Those can be extending or overriden using
/// [`EventMonitor::add_query`] and [`EventMonitor::set_queries`].
pub struct EventMonitor {
    chain_id: ChainId,
    /// WebSocket to collect events from
    client: WebSocketClient,
    /// Async task handle for the WebSocket client's driver
    driver_handle: JoinHandle<()>,
    /// Channel to handler where the monitor for this chain sends the events
    tx_batch: channel::Sender<Result<EventBatch>>,
    /// Channel where to receive client driver errors
    rx_err: mpsc::UnboundedReceiver<tendermint_rpc::Error>,
    /// Channel where to send client driver errors
    tx_err: mpsc::UnboundedSender<tendermint_rpc::Error>,
    /// Channel where to receive commands
    rx_cmd: channel::Receiver<MonitorCmd>,
    /// Node Address
    node_addr: tendermint_rpc::Url,
    /// Queries
    event_queries: Vec<Query>,
    /// All subscriptions combined in a single stream
    subscriptions: Box<SubscriptionStream>,
    /// Tokio runtime
    rt: Arc<TokioRuntime>,
}

impl EventMonitor {
    /// Create an event monitor, and connect to a node
    pub fn new(
        chain_id: ChainId,
        node_addr: tendermint_rpc::Url,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, EventReceiver, TxMonitorCmd)> {
        let (tx_batch, rx_batch) = channel::unbounded();
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let ws_addr = node_addr.clone();
        let (client, driver) = rt
            .block_on(async move { WebSocketClient::new(ws_addr).await })
            .map_err(Error::ClientCreationFailed)?;

        let (tx_err, rx_err) = mpsc::unbounded_channel();
        let websocket_driver_handle = rt.spawn(run_driver(driver, tx_err.clone()));

        // TODO: move them to config file(?)
        let event_queries = vec![Query::from(EventType::Tx), Query::from(EventType::NewBlock)];

        let monitor = Self {
            rt,
            chain_id,
            client,
            driver_handle: websocket_driver_handle,
            event_queries,
            tx_batch,
            rx_err,
            tx_err,
            rx_cmd,
            node_addr,
            subscriptions: Box::new(futures::stream::empty()),
        };

        Ok((monitor, rx_batch, tx_cmd))
    }

    /// Set the queries to subscribe to.
    ///
    /// ## Note
    /// For this change to take effect, one has to [`subscribe`] again.
    pub fn set_queries(&mut self, queries: Vec<Query>) {
        self.event_queries = queries;
    }

    /// Add a new query to subscribe to.
    ///
    /// ## Note
    /// For this change to take effect, one has to [`subscribe`] again.
    pub fn add_query(&mut self, query: Query) {
        self.event_queries.push(query);
    }

    /// Clear the current subscriptions, and subscribe again to all queries.
    pub fn subscribe(&mut self) -> Result<()> {
        let mut subscriptions = vec![];

        for query in &self.event_queries {
            trace!(chain.id = %self.chain_id, "subscribing to query: {}", query);

            let subscription = self
                .rt
                .block_on(self.client.subscribe(query.clone()))
                .map_err(Error::ClientSubscriptionFailed)?;

            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        trace!(chain.id = %self.chain_id, "subscribed to all queries");

        Ok(())
    }

    fn try_reconnect(&mut self) -> Result<()> {
        trace!(chain.id = %self.chain_id,
            "trying to reconnect to WebSocket endpoint {}",
            self.node_addr
        );

        // Try to reconnect
        let (mut client, driver) = self
            .rt
            .block_on(WebSocketClient::new(self.node_addr.clone()))
            .map_err(Error::ClientCreationFailed)?;

        let mut driver_handle = self.rt.spawn(run_driver(driver, self.tx_err.clone()));

        // Swap the new client with the previous one which failed,
        // so that we can shut the latter down gracefully.
        std::mem::swap(&mut self.client, &mut client);
        std::mem::swap(&mut self.driver_handle, &mut driver_handle);

        trace!(
            chain.id = %self.chain_id,
            "reconnected to WebSocket endpoint {}",
            self.node_addr,
        );

        // Shut down previous client
        trace!(chain.id = %self.chain_id, "gracefully shutting down previous client");
        let _ = client.close();

        self.rt
            .block_on(driver_handle)
            .map_err(|e| Error::ClientTerminationFailed(Arc::new(e)))?;

        trace!(chain.id = %self.chain_id, "previous client successfully shutdown");

        Ok(())
    }

    /// Try to resubscribe to events
    fn try_resubscribe(&mut self) -> Result<()> {
        trace!(chain.id = %self.chain_id, "trying to resubscribe to events");
        self.subscribe()
    }

    /// Attempt to restart the WebSocket client using the given retry strategy.
    ///
    /// See the [`retry`](https://docs.rs/retry) crate and the
    /// [`crate::util::retry`] module for more information.
    fn restart(&mut self) {
        let result = retry_with_index(retry_strategy::default(), |_| {
            // Try to reconnect
            if let Err(e) = self.try_reconnect() {
                trace!(chain.id = %self.chain_id, "error when reconnecting: {}", e);
                return RetryResult::Retry(());
            }

            // Try to resubscribe
            if let Err(e) = self.try_resubscribe() {
                trace!(chain.id = %self.chain_id, "error when reconnecting: {}", e);
                return RetryResult::Retry(());
            }

            RetryResult::Ok(())
        });

        match result {
            Ok(()) => info!(
                chain.id = %self.chain_id,
                "successfully reconnected to WebSocket endpoint {}",
                self.node_addr
            ),
            Err(retries) => error!(
                chain.id = %self.chain_id,
                "failed to reconnect to {} after {} retries",
                self.node_addr, retry_count(&retries)
            ),
        }
    }

    /// Event monitor loop
    #[allow(clippy::while_let_loop)]
    pub fn run(mut self) {
        debug!(chain.id = %self.chain_id, "starting event monitor");

        // Continuously run the event loop, so that when it aborts
        // because of WebSocket client restart, we pick up the work again.
        loop {
            match self.run_loop() {
                Next::Continue => continue,
                Next::Abort => break,
            }
        }

        debug!(chain.id = %self.chain_id, "event monitor is shutting down");

        // Close the WebSocket connection
        let _ = self.client.close();

        // Wait for the WebSocket driver to finish
        let _ = self.rt.block_on(self.driver_handle);

        trace!(chain.id = %self.chain_id, "event monitor has successfully shut down");
    }

    fn run_loop(&mut self) -> Next {
        // Take ownership of the subscriptions
        let subscriptions =
            std::mem::replace(&mut self.subscriptions, Box::new(futures::stream::empty()));

        // Convert the stream of RPC events into a stream of event batches.
        let batches = stream_batches(subscriptions, self.chain_id.clone());

        // Needed to be able to poll the stream
        pin_mut!(batches);

        // Work around double borrow
        let rt = self.rt.clone();

        loop {
            if let Ok(cmd) = self.rx_cmd.try_recv() {
                match cmd {
                    MonitorCmd::Shutdown => return Next::Abort,
                }
            }

            let result = rt.block_on(async {
                tokio::select! {
                    Some(batch) = batches.next() => Ok(batch),
                    Some(err) = self.rx_err.recv() => Err(Error::WebSocketDriver(err)),
                }
            });

            match result {
                Ok(batch) => self.process_batch(batch).unwrap_or_else(|e| {
                    warn!(chain.id = %self.chain_id, "{}", e);
                }),
                Err(e) => {
                    error!(chain.id = %self.chain_id, "failed to collect events: {}", e);

                    // Restart the event monitor, reconnect to the WebSocket endpoint,
                    // and subscribe again to the queries.
                    self.restart();

                    // Abort this event loop, the `run` method will start a new one.
                    // We can't just write `return self.run()` here because Rust
                    // does not perform tail call optimization, and we would
                    // thus potentially blow up the stack after many restarts.
                    break;
                }
            }
        }

        Next::Continue
    }

    /// Collect the IBC events from the subscriptions
    fn process_batch(&self, batch: EventBatch) -> Result<()> {
        self.tx_batch
            .send(Ok(batch))
            .map_err(|_| Error::ChannelSendFailed)?;

        Ok(())
    }
}

/// Collect the IBC events from an RPC event
fn collect_events(chain_id: &ChainId, event: RpcEvent) -> impl Stream<Item = (Height, IbcEvent)> {
    let events = crate::event::rpc::get_all_events(chain_id, event).unwrap_or_default();
    stream::iter(events)
}

/// Convert a stream of RPC event into a stream of event batches
fn stream_batches(
    subscriptions: Box<SubscriptionStream>,
    chain_id: ChainId,
) -> impl Stream<Item = EventBatch> {
    let id = chain_id.clone();

    // Collect IBC events from each RPC event
    let events = subscriptions
        .filter_map(|rpc_event| async { rpc_event.ok() })
        .flat_map(move |rpc_event| collect_events(&id, rpc_event));

    // Group events by height
    let grouped = group_while(events, |(h0, _), (h1, _)| h0 == h1);

    // Convert each group to a batch
    grouped.map(move |events| {
        let height = events
            .first()
            .map(|(h, _)| h)
            .copied()
            .expect("internal error: found empty group"); // SAFETY: upheld by `group_while`

        let mut events = events.into_iter().map(|(_, e)| e).collect();
        sort_events(&mut events);

        EventBatch {
            height,
            events,
            chain_id: chain_id.clone(),
        }
    })
}

/// Sort the given events by putting the NewBlock event first,
/// and leaving the other events as is.
fn sort_events(events: &mut Vec<IbcEvent>) {
    events.sort_by(|a, b| match (a, b) {
        (IbcEvent::NewBlock(_), _) => Ordering::Less,
        _ => Ordering::Equal,
    })
}

async fn run_driver(
    driver: WebSocketClientDriver,
    tx: mpsc::UnboundedSender<tendermint_rpc::Error>,
) {
    if let Err(e) = driver.run().await {
        if tx.send(e).is_err() {
            error!("failed to relay driver error to event monitor");
        }
    }
}

pub enum Next {
    Abort,
    Continue,
}
