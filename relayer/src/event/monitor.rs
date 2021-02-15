use std::sync::Arc;

use anomaly::BoxError;
use crossbeam_channel as channel;
use futures::stream::StreamExt;
use futures::{stream::select_all, Stream};
use itertools::Itertools;
use tendermint::net;
use tendermint_rpc::{query::EventType, query::Query, SubscriptionClient, WebSocketClient};
use tokio::runtime::Runtime as TokioRuntime;
use tokio::task::JoinHandle;
use tracing::{debug, error, info};

use ibc::{events::IBCEvent, ics24_host::identifier::ChainId};

use crate::error::{Error, Kind};
use ibc::ics02_client::height::Height;

/// A batch of events from a chain at a specific height
#[derive(Clone, Debug)]
pub struct EventBatch {
    pub chain_id: ChainId,
    pub height: Height,
    pub events: Vec<IBCEvent>,
}

type SubscriptionResult = Result<tendermint_rpc::event::Event, tendermint_rpc::Error>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

/// Connect to a TM node, receive push events over a websocket and filter them for the
/// event handler.
pub struct EventMonitor {
    chain_id: ChainId,
    /// WebSocket to collect events from
    websocket_client: WebSocketClient,
    /// Async task handle for the WebSocket client's driver
    websocket_driver_handle: JoinHandle<tendermint_rpc::Result<()>>,
    /// Channel to handler where the monitor for this chain sends the events
    tx_batch: channel::Sender<EventBatch>,
    /// Node Address
    node_addr: net::Address,
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
        rpc_addr: net::Address,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, channel::Receiver<EventBatch>), Error> {
        let (tx, rx) = channel::unbounded();

        let websocket_addr = rpc_addr.clone();
        let (websocket_client, websocket_driver) = rt.block_on(async move {
            WebSocketClient::new(websocket_addr.clone())
                .await
                .map_err(|e| Kind::Rpc(websocket_addr).context(e))
        })?;

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
            node_addr: rpc_addr,
            subscriptions: Box::new(futures::stream::empty()),
        };

        Ok((monitor, rx))
    }

    /// Clear the current subscriptions, and subscribe again to all queries.
    pub fn subscribe(&mut self) -> Result<(), BoxError> {
        let mut subscriptions = vec![];

        for query in &self.event_queries {
            let subscription = self
                .rt
                .block_on(self.websocket_client.subscribe(query.clone()))?;

            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        Ok(())
    }

    fn try_reconnect(&mut self) -> Result<(), BoxError> {
        // Try to reconnect
        let (mut websocket_client, websocket_driver) = self
            .rt
            .block_on(WebSocketClient::new(self.node_addr.clone()))?;

        let mut websocket_driver_handle = self.rt.spawn(websocket_driver.run());

        // Swap the new client with the previous one which failed,
        // so that we can shut the latter down gracefully.
        std::mem::swap(&mut self.websocket_client, &mut websocket_client);
        std::mem::swap(
            &mut self.websocket_driver_handle,
            &mut websocket_driver_handle,
        );

        debug!("Reconnected");

        // Shut down previous client
        debug!("Gracefully shutting down previous client");

        if let Err(e) = websocket_client.close() {
            error!("Previous websocket client closing failure {}", e);
        }

        self.rt.block_on(websocket_driver_handle).map_err(|e| {
            tendermint_rpc::Error::client_internal_error(format!(
                "failed to terminate previous WebSocket client driver: {}",
                e
            ))
        })??;

        Ok(())
    }

    /// Try to resubscribe to events
    fn try_resubscribe(&mut self) -> Result<(), BoxError> {
        self.subscribe()
    }

    /// Event monitor loop
    pub fn run(mut self) {
        info!(chain.id = %self.chain_id, "running listener");

        loop {
            match self.collect_events() {
                Ok(_) => continue,
                Err(err) => {
                    debug!("Web socket error: {}", err);

                    // Try to reconnect
                    self.try_reconnect().unwrap_or_else(|e| {
                        debug!("Error on reconnecting: {}", e);
                        panic!("Abort during reconnection");
                    });

                    // Try to resubscribe
                    self.try_resubscribe().unwrap_or_else(|e| {
                        debug!("Error on reconnecting: {}", e);
                        panic!("Abort during reconnection");
                    });
                }
            }
        }
    }

    /// Collect the IBC events from the subscriptions
    fn collect_events(&mut self) -> Result<(), BoxError> {
        let event = self.rt.block_on(self.subscriptions.next());

        match event {
            Some(Ok(event)) => {
                match crate::event::rpc::get_all_events(&self.chain_id, event.clone()) {
                    Ok(ibc_events) => {
                        let events_by_height = ibc_events.into_iter().into_group_map();

                        for (height, events) in events_by_height {
                            let batch = EventBatch {
                                chain_id: self.chain_id.clone(),
                                height,
                                events,
                            };
                            self.tx_batch.send(batch)?;
                        }
                    }
                    Err(err) => {
                        error!(
                            "Error {} when extracting IBC events from {:?}: ",
                            err, event
                        );
                    }
                }
            }
            Some(Err(err)) => {
                error!("Error on collecting events from subscriptions: {}", err);
            }
            None => (), // no events available
        }

        Ok(())
    }
}
