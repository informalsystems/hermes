use ibc::events::IBCEvent;
use tendermint::{chain, net, Error as TMError};
use tendermint_rpc::{
    query::EventType, query::Query, Subscription, SubscriptionClient, WebSocketClient,
};
use tokio::stream::StreamExt;
use tokio::sync::mpsc::Sender;

use futures::{stream::select_all, Stream};
use tracing::{debug, error, info};

type SubscriptionResult = Result<tendermint_rpc::event::Event, tendermint_rpc::Error>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

/// Connect to a TM node, receive push events over a websocket and filter them for the
/// event handler.
pub struct EventMonitor {
    chain_id: chain::Id,
    /// Websocket to collect events from
    websocket_client: WebSocketClient,
    /// Channel to handler where the monitor for this chain sends the events
    channel_to_handler: Sender<(chain::Id, Vec<IBCEvent>)>,
    /// Node Address
    node_addr: net::Address,
    /// Queries
    event_queries: Vec<Query>,
    /// All subscriptions combined in a single stream
    subscriptions: Box<SubscriptionStream>,
}

impl EventMonitor {
    /// Create an event monitor, connect to a node and subscribe to queries.
    pub async fn create(
        chain_id: chain::Id,
        rpc_addr: net::Address,
        channel_to_handler: Sender<(chain::Id, Vec<IBCEvent>)>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let websocket_client = WebSocketClient::new(rpc_addr.clone()).await?;

        // TODO: move them to config file(?)
        let event_queries = vec![Query::from(EventType::Tx), Query::from(EventType::NewBlock)];

        Ok(EventMonitor {
            chain_id,
            websocket_client,
            channel_to_handler,
            node_addr: rpc_addr.clone(),
            event_queries,
            subscriptions: Box::new(futures::stream::empty()),
        })
    }

    /// Clear the current subscriptions, and subscribe again to all queries.
    pub async fn subscribe(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut subscriptions = vec![];

        for query in &self.event_queries {
            let subscription = self.websocket_client.subscribe(query.clone()).await?;
            subscriptions.push(subscription);
        }

        self.subscriptions = Box::new(select_all(subscriptions));

        Ok(())
    }

    /// Event monitor loop
    pub async fn run(&mut self) {
        info!(chain.id = % self.chain_id, "running listener for");

        loop {
            match self.collect_events().await {
                Ok(..) => continue,
                Err(err) => {
                    debug!("Web socket error: {}", err);

                    // Try to reconnect
                    let mut websocket_client = WebSocketClient::new(self.node_addr.clone())
                        .await
                        .unwrap_or_else(|e| {
                            debug!("Error on reconnection: {}", e);
                            panic!("Abort on failed reconnection");
                        });

                    // Swap the new client with the previous one which failed,
                    // so that we can shut the latter down gracefully.
                    std::mem::swap(&mut self.websocket_client, &mut websocket_client);

                    debug!("Reconnected");

                    // Shut down previous client
                    debug!("Gracefully shutting down previous client");
                    websocket_client.close().await.unwrap_or_else(|e| {
                        error!("Failed to close previous WebSocket client: {}", e);
                    });

                    // Try to resubscribe
                    if let Err(err) = self.subscribe().await {
                        debug!("Error on recreating subscriptions: {}", err);
                        panic!("Abort during reconnection");
                    };
                }
            }
        }
    }

    /// Collect the IBC events from the subscriptions
    pub async fn collect_events(&mut self) -> Result<(), TMError> {
        tokio::select! {
            Some(event) = self.subscriptions.next() => {
                match event {
                    Ok(event) => {
                        if let Ok(ibc_events) = ibc::events::get_all_events(event) {
                            // TODO - send_timeout()?
                            self.channel_to_handler
                                .send((self.chain_id, ibc_events))
                                .await?;
                        }
                    }
                    Err(err) => {
                        error!("Error on collecting events from subscriptions: {}", err);
                    }
                }
            },
        }

        Ok(())
    }
}
