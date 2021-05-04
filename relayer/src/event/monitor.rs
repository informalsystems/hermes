use std::sync::Arc;

use crossbeam_channel as channel;
use futures::stream::StreamExt;
use futures::{stream::select_all, Stream};
use itertools::Itertools;
use tendermint_rpc::{query::EventType, query::Query, SubscriptionClient, WebSocketClient};
use thiserror::Error;
use tokio::runtime::Runtime as TokioRuntime;
use tokio::task::JoinHandle;
use tracing::{debug, error, info, warn};

use ibc::{events::IbcEvent, ics02_client::height::Height, ics24_host::identifier::ChainId};

#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error("failed to create WebSocket client driver: {0}")]
    ClientCreationFailed(tendermint_rpc::Error),

    #[error("failed to terminate previous WebSocket client driver: {0}")]
    ClientTerminationFailed(Arc<tokio::task::JoinError>),

    #[error("failed to run previous WebSocket client driver to completion: {0}")]
    ClientCompletionFailed(tendermint_rpc::Error),

    #[error("failed to subscribe to events via WebSocket client: {0}")]
    ClientSubscriptionFailed(tendermint_rpc::Error),

    #[error("failed to collect events over WebSocket subscription: {0}")]
    NextEventBatchFailed(tendermint_rpc::Error),

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

impl EventBatch {
    pub fn unwrap_or_clone(self: Arc<Self>) -> Self {
        Arc::try_unwrap(self).unwrap_or_else(|batch| batch.as_ref().clone())
    }
}

type SubscriptionResult = Result<tendermint_rpc::event::Event, tendermint_rpc::Error>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

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
    websocket_client: WebSocketClient,
    /// Async task handle for the WebSocket client's driver
    websocket_driver_handle: JoinHandle<tendermint_rpc::Result<()>>,
    /// Channel to handler where the monitor for this chain sends the events
    tx_batch: channel::Sender<EventBatch>,
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
    ) -> Result<(Self, channel::Receiver<EventBatch>), Error> {
        let (tx, rx) = channel::unbounded();

        let ws_addr = node_addr.clone();
        let (websocket_client, websocket_driver) = rt
            .block_on(async move { WebSocketClient::new(ws_addr.clone()).await })
            .map_err(Error::ClientCreationFailed)?;

        let websocket_driver_handle = rt.spawn(websocket_driver.run());

        // TODO: move them to config file(?)
        let event_queries = vec![Query::from(EventType::Tx), Query::from(EventType::NewBlock)];

        let monitor = Self {
            rt,
            chain_id,
            websocket_client,
            websocket_driver_handle,
            event_queries,
            tx_batch: tx,
            node_addr,
            subscriptions: Box::new(futures::stream::empty()),
        };

        Ok((monitor, rx))
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
    pub fn subscribe(&mut self) -> Result<(), Error> {
        let mut subscriptions = vec![];

        for query in &self.event_queries {
            debug!("subscribing to query: {}", query);

            let subscription = self
                .rt
                .block_on(self.websocket_client.subscribe(query.clone()))
                .map_err(Error::ClientSubscriptionFailed)?;

            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        debug!("subscribed to all queries");

        Ok(())
    }

    fn try_reconnect(&mut self) -> Result<(), Error> {
        warn!(
            "trying to reconnect to WebSocket endpoint: {}",
            self.node_addr
        );

        // Try to reconnect
        let (mut websocket_client, websocket_driver) = self
            .rt
            .block_on(WebSocketClient::new(self.node_addr.clone()))
            .map_err(Error::ClientCreationFailed)?;

        let mut websocket_driver_handle = self.rt.spawn(websocket_driver.run());

        // Swap the new client with the previous one which failed,
        // so that we can shut the latter down gracefully.
        std::mem::swap(&mut self.websocket_client, &mut websocket_client);
        std::mem::swap(
            &mut self.websocket_driver_handle,
            &mut websocket_driver_handle,
        );

        warn!("reconnected to WebSocket endpoint: {}", self.node_addr);

        // Shut down previous client
        debug!("gracefully shutting down previous client");

        if let Err(e) = websocket_client.close() {
            error!("previous websocket client closing failure {}", e);
        }

        let result = self
            .rt
            .block_on(websocket_driver_handle)
            .map_err(|e| Error::ClientTerminationFailed(Arc::new(e)))?;

        debug!("previous client successfully shutdown");

        result.map_err(Error::ClientCompletionFailed)
    }

    /// Try to resubscribe to events
    fn try_resubscribe(&mut self) -> Result<(), Error> {
        warn!("trying to resubscribe to events");

        self.subscribe()
    }

    /// Event monitor loop
    pub fn run(mut self) {
        info!(chain.id = %self.chain_id, "starting event monitor");

        loop {
            match self.collect_events() {
                Ok(batches) => self.process_batches(batches).unwrap_or_else(|e| {
                    error!("failed to process event batch: {}", e);
                }),
                Err(e) => {
                    error!("failed to collect events: {}", e);

                    // Try to reconnect
                    self.try_reconnect().unwrap_or_else(|e| {
                        error!("error on reconnecting: {}", e);
                    });

                    // Try to resubscribe
                    self.try_resubscribe().unwrap_or_else(|e| {
                        error!("error on reconnecting: {}", e);
                    });
                }
            }
        }
    }

    /// Collect the IBC events from the subscriptions
    fn process_batches(&self, batches: Vec<EventBatch>) -> Result<(), Error> {
        for batch in batches {
            self.tx_batch
                .send(batch)
                .map_err(|_| Error::ChannelSendFailed)?;
        }

        Ok(())
    }

    /// Collect the IBC events from the subscriptions
    fn collect_events(&mut self) -> Result<Vec<EventBatch>, Error> {
        if let Some(event) = self.rt.block_on(self.subscriptions.next()) {
            let event = event.map_err(Error::NextEventBatchFailed)?;
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
        } else {
            Ok(vec![])
        }
    }
}
