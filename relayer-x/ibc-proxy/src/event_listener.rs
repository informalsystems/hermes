use std::cmp::Ordering;

use futures::{
    pin_mut,
    stream::{self, select_all, StreamExt},
    Stream, TryStreamExt,
};

use tokio::sync::mpsc;
use tokio::task::JoinHandle;
use tracing::{debug, error, info, trace};

use tendermint_rpc::{
    event::Event as RpcEvent, query::Query, Error as RpcError, SubscriptionClient, Url,
    WebSocketClient, WebSocketClientDriver,
};

use ibc::{core::ics02_client::height::Height, events::IbcEvent};

use crate::utils::stream::try_group_while;

pub type Result<T> = std::result::Result<T, Error>;

/// A batch of events from a chain at a specific height
#[derive(Clone, Debug)]
pub struct EventBatch {
    pub height: Height,
    pub events: Vec<IbcEvent>,
}

type SubscriptionResult = core::result::Result<RpcEvent, RpcError>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

pub type EventSender = mpsc::UnboundedSender<Result<EventBatch>>;
pub type EventReceiver = mpsc::UnboundedReceiver<Result<EventBatch>>;
pub type MonitorCmdSender = mpsc::UnboundedSender<MonitorCmd>;

#[derive(Debug)]
pub enum MonitorCmd {
    Shutdown,
}

/// Connect to a Tendermint node, subscribe to a set of queries,
/// receive push events over a websocket, and filter them for the
/// event handler.
///
/// The default events that are queried are:
/// - [`EventType::NewBlock`](tendermint_rpc::query::EventType::NewBlock)
/// - [`EventType::Tx`](tendermint_rpc::query::EventType::Tx)
pub struct EventMonitor {
    /// WebSocket to collect events from
    client: WebSocketClient,
    /// Async task handle for the WebSocket client's driver
    driver_handle: JoinHandle<()>,
    /// Channel to handler where the monitor for this chain sends the events
    tx_batch: mpsc::UnboundedSender<Result<EventBatch>>,
    /// Channel where to receive client driver errors
    rx_err: mpsc::UnboundedReceiver<tendermint_rpc::Error>,
    /// Channel where to send client driver errors
    tx_err: mpsc::UnboundedSender<tendermint_rpc::Error>,
    /// Channel where to receive commands
    rx_cmd: mpsc::UnboundedReceiver<MonitorCmd>,
    /// Node Address
    node_addr: Url,
    /// Queries
    event_queries: Vec<Query>,
    /// All subscriptions combined in a single stream
    subscriptions: Box<SubscriptionStream>,
}

// TODO: These are SDK specific, should be eventually moved.
pub mod queries {
    use tendermint_rpc::query::{EventType, Query};

    pub fn all() -> Vec<Query> {
        // Note: Tendermint-go supports max 5 query specifiers!
        vec![
            new_block(),
            ibc_client(),
            ibc_connection(),
            ibc_channel(),
            // This will be needed when we send misbehavior evidence to full node
            // Query::eq("message.module", "evidence"),
        ]
    }

    pub fn new_block() -> Query {
        Query::from(EventType::NewBlock)
    }

    pub fn ibc_client() -> Query {
        Query::eq("message.module", "ibc_client")
    }

    pub fn ibc_connection() -> Query {
        Query::eq("message.module", "ibc_connection")
    }

    pub fn ibc_channel() -> Query {
        Query::eq("message.module", "ibc_channel")
    }
}

impl EventMonitor {
    /// Create an event monitor, and connect to a node
    pub async fn new(node_addr: Url) -> Result<(Self, EventReceiver, MonitorCmdSender)> {
        let (tx_batch, rx_batch) = mpsc::unbounded_channel();
        let (tx_cmd, rx_cmd) = mpsc::unbounded_channel();

        let ws_addr = node_addr.clone();
        let (client, driver) = WebSocketClient::new(ws_addr)
            .await
            .map_err(|_| Error::client_creation_failed(node_addr.clone()))?;

        let (tx_err, rx_err) = mpsc::unbounded_channel();
        let websocket_driver_handle = tokio::task::spawn(run_driver(driver, tx_err.clone()));

        let event_queries = queries::all();

        let monitor = Self {
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

    /// The list of [`Query`] that this event monitor is subscribing for.
    pub fn queries(&self) -> &[Query] {
        &self.event_queries
    }

    /// Clear the current subscriptions, and subscribe again to all queries.
    pub async fn subscribe(&mut self) -> Result<()> {
        let mut subscriptions = vec![];

        for query in &self.event_queries {
            trace!("subscribing to query: {}", query);

            let subscription = self
                .client
                .subscribe(query.clone())
                .await
                .map_err(Error::client_subscription_failed)?;

            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        trace!("subscribed to all queries");

        Ok(())
    }

    async fn try_reconnect(&mut self) -> Result<()> {
        trace!(
            "trying to reconnect to WebSocket endpoint {}",
            self.node_addr
        );

        // Try to reconnect
        let (mut client, driver) = WebSocketClient::new(self.node_addr.clone())
            .await
            .map_err(|_| Error::client_creation_failed(self.node_addr.clone()))?;

        let mut driver_handle = tokio::task::spawn(run_driver(driver, self.tx_err.clone()));

        // Swap the new client with the previous one which failed,
        // so that we can shut the latter down gracefully.
        core::mem::swap(&mut self.client, &mut client);
        core::mem::swap(&mut self.driver_handle, &mut driver_handle);

        trace!("reconnected to WebSocket endpoint {}", self.node_addr);

        // Shut down previous client
        trace!("gracefully shutting down previous client",);

        let _ = client.close();

        driver_handle
            .await
            .map_err(Error::client_termination_failed)?;

        trace!("previous client successfully shutdown");

        Ok(())
    }

    /// Try to resubscribe to events
    async fn try_resubscribe(&mut self) -> Result<()> {
        trace!("trying to resubscribe to events");
        self.subscribe().await
    }

    /// Attempt to reconnect the WebSocket client using the given retry strategy.
    ///
    /// See the [`retry`](https://docs.rs/retry) crate and the
    /// [`crate::util::retry`] module for more information.
    async fn reconnect(&mut self) {
        let result = {
            if let Err(e) = self.try_reconnect().await {
                trace!("error when reconnecting: {}", e);
                Err(e)
            } else if let Err(e) = self.try_resubscribe().await {
                trace!("error when resubscribing: {}", e);
                Err(e)
            } else {
                Ok(())
            }
        };

        match result {
            Ok(()) => info!(
                "successfully reconnected to WebSocket endpoint {}",
                self.node_addr
            ),
            Err(e) => error!(
                "failed to reconnect to {} after exhausting retries, reason: {}",
                self.node_addr, e
            ),
        }
    }

    /// Event monitor loop
    pub async fn run(mut self) {
        debug!("starting event monitor");

        // Continuously run the event loop, so that when it aborts
        // because of WebSocket client restart, we pick up the work again.
        while let Next::Continue = self.run_loop().await {
            continue;
        }

        debug!("event monitor is shutting down");

        // Close the WebSocket connection
        let _ = self.client.close();

        // Wait for the WebSocket driver to finish
        let _ = self.driver_handle.await;

        trace!("event monitor has successfully shut down",);
    }

    async fn run_loop(&mut self) -> Next {
        // Take ownership of the subscriptions
        let subscriptions =
            core::mem::replace(&mut self.subscriptions, Box::new(futures::stream::empty()));

        // Convert the stream of RPC events into a stream of event batches.
        let batches = stream_batches(subscriptions);

        // Needed to be able to poll the stream
        pin_mut!(batches);

        loop {
            if let Ok(MonitorCmd::Shutdown) = self.rx_cmd.try_recv() {
                return Next::Abort;
            }

            let result = tokio::select! {
                Some(batch) = batches.next() => batch,
                Some(e) = self.rx_err.recv() => Err(Error::web_socket_driver(e)),
            };

            // Repeat check of shutdown command here, as previous recv()
            // may block for a long time.
            if let Ok(MonitorCmd::Shutdown) = self.rx_cmd.try_recv() {
                return Next::Abort;
            }

            match result {
                Ok(batch) => self.process_batch(batch).unwrap_or_else(|e| {
                    error!("batch processing failed, reason: {}", e);
                }),
                Err(e) => {
                    match e.detail() {
                        ErrorDetail::SubscriptionCancelled(reason) => {
                            error!("subscription cancelled, reason: {}", reason);

                            self.propagate_error(e).unwrap_or_else(|e| {
                                error!("{}", e);
                            });

                            // Reconnect to the WebSocket endpoint, and subscribe again to the queries.
                            self.reconnect().await;

                            // Abort this event loop, the `run` method will start a new one.
                            // We can't just write `return self.run()` here because Rust
                            // does not perform tail call optimization, and we would
                            // thus potentially blow up the stack after many restarts.
                            return Next::Continue;
                        }
                        _ => {
                            error!("failed to collect events: {}", e);

                            // Reconnect to the WebSocket endpoint, and subscribe again to the queries.
                            self.reconnect().await;

                            // Abort this event loop, the `run` method will start a new one.
                            // We can't just write `return self.run()` here because Rust
                            // does not perform tail call optimization, and we would
                            // thus potentially blow up the stack after many restarts.
                            return Next::Continue;
                        }
                    }
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
    fn propagate_error(&self, error: Error) -> Result<()> {
        self.tx_batch
            .send(Err(error))
            .map_err(|_| Error::channel_send_failed())?;

        Ok(())
    }

    /// Collect the IBC events from the subscriptions
    fn process_batch(&self, batch: EventBatch) -> Result<()> {
        self.tx_batch
            .send(Ok(batch))
            .map_err(|_| Error::channel_send_failed())?;

        Ok(())
    }
}

/// Collect the IBC events from an RPC event
fn collect_events(event: RpcEvent) -> impl Stream<Item = Result<(Height, IbcEvent)>> {
    let events = crate::utils::event::get_all_events(0, event).unwrap_or_default(); // FIXME(romac)
    stream::iter(events).map(Ok)
}

/// Convert a stream of RPC event into a stream of event batches
fn stream_batches(
    subscriptions: Box<SubscriptionStream>,
) -> impl Stream<Item = Result<EventBatch>> {
    // Collect IBC events from each RPC event
    let events = subscriptions
        .map_ok(collect_events)
        .map_err(Error::canceled_or_generic)
        .try_flatten();

    // Group events by height
    let grouped = try_group_while(events, |(h0, _), (h1, _)| h0 == h1);

    // Convert each group to a batch
    grouped.map_ok(move |events| {
        let height = events
            .first()
            .map(|(h, _)| h)
            .copied()
            .expect("internal error: found empty group"); // SAFETY: upheld by `group_while`

        let mut events = events.into_iter().map(|(_, e)| e).collect::<Vec<_>>();
        sort_events(&mut events);

        EventBatch { height, events }
    })
}

/// Sort the given events by putting the NewBlock event first,
/// and leaving the other events as is.
fn sort_events(events: &mut [IbcEvent]) {
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

use flex_error::{define_error, TraceError};

define_error! {
    #[derive(Debug, Clone)]
    Error {
        WebSocketDriver
            [ TraceError<RpcError> ]
            |_| { "WebSocket driver failed" },

        ClientCreationFailed
            { address: Url }
            |e| { format_args!("failed to create WebSocket driver listening on {}", e.address) },

        ClientTerminationFailed
            [ TraceError<tokio::task::JoinError> ]
            |_| { "failed to terminate previous WebSocket driver" },

        ClientCompletionFailed
            [ TraceError<RpcError> ]
            |_| { "failed to run previous WebSocket driver to completion" },

        ClientSubscriptionFailed
            [ TraceError<RpcError> ]
            |_| { "failed to run previous WebSocket driver to completion" },

        NextEventBatchFailed
            [ TraceError<RpcError> ]
            |_| { "failed to collect events over WebSocket subscription" },

        CollectEventsFailed
            { reason: String }
            |e| { format_args!("failed to extract IBC events: {0}", e.reason) },

        ChannelSendFailed
            |_| { "internal message-passing failure: monitor could not reach chain handler" },

        SubscriptionCancelled
            [ TraceError<RpcError> ]
            |_| { "subscription cancelled" },

        Rpc
            [ TraceError<RpcError> ]
            |_| { "RPC error" },
    }
}

impl Error {
    pub fn canceled_or_generic(e: RpcError) -> Self {
        use tendermint_rpc::error::ErrorDetail;

        match e.detail() {
            ErrorDetail::Server(detail) if detail.reason.contains("subscription was cancelled") => {
                Self::subscription_cancelled(e)
            }
            _ => Self::rpc(e),
        }
    }
}
