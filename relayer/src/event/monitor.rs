use std::sync::Arc;

use crossbeam_channel as channel;
use futures::stream::StreamExt;
use futures::{stream::select_all, Stream};
use itertools::Itertools;
use thiserror::Error;
use tokio::task::JoinHandle;
use tokio::{runtime::Runtime as TokioRuntime, sync::mpsc};
use tracing::{debug, error, info, warn};

use tendermint_rpc::{
    event::Event as RpcEvent,
    query::{EventType, Query},
    Error as RpcError, Result as RpcResult, SubscriptionClient, WebSocketClient,
    WebSocketClientDriver,
};

use ibc::{events::IbcEvent, ics02_client::height::Height, ics24_host::identifier::ChainId};

use crate::util::retry::Clamped;

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

    #[error("failed to send event batch through channel")]
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

pub type EventReceiver = channel::Receiver<Result<EventBatch>>;

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
    /// Node Address
    node_addr: tendermint_rpc::Url,
    /// Queries
    event_queries: Vec<Query>,
    /// All subscriptions combined in a single stream
    subscriptions: Box<SubscriptionStream>,
    /// Tokio runtime
    rt: Arc<TokioRuntime>,
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

impl EventMonitor {
    /// Create an event monitor, and connect to a node
    pub fn new(
        chain_id: ChainId,
        node_addr: tendermint_rpc::Url,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, EventReceiver)> {
        let (tx_batch, rx_batch) = channel::unbounded();

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
            node_addr,
            subscriptions: Box::new(futures::stream::empty()),
        };

        Ok((monitor, rx_batch))
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
            debug!("subscribing to query: {}", query);

            let subscription = self
                .rt
                .block_on(self.client.subscribe(query.clone()))
                .map_err(Error::ClientSubscriptionFailed)?;

            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        debug!("subscribed to all queries");

        Ok(())
    }

    fn try_reconnect(&mut self) -> Result<()> {
        warn!(
            "trying to reconnect to WebSocket endpoint: {}",
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

        warn!("reconnected to WebSocket endpoint: {}", self.node_addr);

        // Shut down previous client
        debug!("gracefully shutting down previous client");

        if let Err(e) = client.close() {
            error!("previous websocket client closing failure {}", e);
        }

        self.rt
            .block_on(driver_handle)
            .map_err(|e| Error::ClientTerminationFailed(Arc::new(e)))?;

        debug!("previous client successfully shutdown");

        Ok(())
    }

    /// Try to resubscribe to events
    fn try_resubscribe(&mut self) -> Result<()> {
        warn!("trying to resubscribe to events");

        self.subscribe()
    }

    /// Attempt to restart the WebSocket client using the given retry strategy.
    ///
    /// See the [`retry`](https://docs.rs/retry) crate and the
    /// [`crate::util::retry`] module for more information.
    fn restart(&mut self) {
        use retry::{retry_with_index, OperationResult as TryResult};

        let strategy = Clamped::default();

        retry_with_index(strategy.iter(), |index| {
            // Try to reconnect
            if let Err(e) = self.try_reconnect() {
                error!("error when reconnecting: {}", e);
                return TryResult::Retry(index);
            }

            // Try to resubscribe
            if let Err(e) = self.try_resubscribe() {
                error!("error when reconnecting: {}", e);
                return TryResult::Retry(index);
            }

            TryResult::Ok(())
        })
        .unwrap_or_else(|retries| error!("failed to reconnect after {} retries", retries));
    }

    /// Event monitor loop
    pub fn run(mut self) {
        info!(chain.id = %self.chain_id, "starting event monitor");

        let rt = self.rt.clone();

        loop {
            let result = rt.block_on(async {
                tokio::select! {
                    Some(event) = self.subscriptions.next() => {
                        event
                            .map_err(Error::NextEventBatchFailed)
                            .and_then(|e| self.collect_events(e))
                    },
                    Some(e) = self.rx_err.recv() => Err(Error::WebSocketDriver(e)),
                }
            });

            match result {
                Ok(batches) => self.process_batches(batches).unwrap_or_else(|e| {
                    error!("failed to process event batch: {}", e);
                }),
                Err(e) => {
                    error!("failed to collect events: {}", e);

                    // Restart the event monitor
                    self.restart();
                }
            }
        }
    }

    /// Collect the IBC events from the subscriptions
    fn process_batches(&self, batches: Vec<EventBatch>) -> Result<()> {
        for batch in batches {
            self.tx_batch
                .send(Ok(batch))
                .map_err(|_| Error::ChannelSendFailed)?;
        }

        Ok(())
    }

    /// Collect the IBC events from the subscriptions
    fn collect_events(&mut self, event: RpcEvent) -> Result<Vec<EventBatch>> {
        let ibc_events = crate::event::rpc::get_all_events(&self.chain_id, event)
            .map_err(Error::CollectEventsFailed)?;

        let events_by_height = ibc_events.into_iter().into_group_map();
        let batches = events_by_height
            .into_iter()
            .map(|(height, events)| EventBatch {
                chain_id: self.chain_id.clone(),
                height,
                events,
            })
            .collect();

        Ok(batches)
    }
}
