use ibc::events::IBCEvent;
use tendermint::{chain, net, Error as TMError};
use tendermint_rpc::Subscription;
use tendermint_rpc::{SubscriptionClient, WebSocketClient};
use tokio::stream::StreamExt;
use tokio::sync::mpsc::Sender;

use futures::stream::select_all;
use tracing::{debug, info};

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
    event_queries: Vec<String>,
    /// Subscriptions
    subscriptions: Vec<Subscription>,
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
        let event_queries = vec![
            "tm.event='NewTx'".to_string(),
            "tm.event='NewBlock'".to_string(),
        ];

        Ok(EventMonitor {
            chain_id,
            websocket_client,
            channel_to_handler,
            node_addr: rpc_addr.clone(),
            subscriptions: Vec::with_capacity(event_queries.len()),
            event_queries,
        })
    }

    /// Terminate and clear the current subscriptions, and subscribe again to all queries.
    pub async fn subscribe(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let count = self.subscriptions.len();
        let subscriptions = std::mem::replace(&mut self.subscriptions, Vec::with_capacity(count));

        for subscription in subscriptions {
            subscription.terminate().await?;
        }

        for query in &self.event_queries {
            let subscription = self.websocket_client.subscribe(query.clone()).await?;
            self.subscriptions.push(subscription);
        }

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
                    let websocket_client = WebSocketClient::new(self.node_addr.clone())
                        .await
                        .unwrap_or_else(|e| {
                            debug!("Error on reconnection {}", e);
                            panic!("Abort on failed reconnection")
                        });

                    debug!("Reconnected");
                    self.websocket_client = websocket_client;

                    // Try to resubscribe
                    if let Err(err) = self.subscribe().await {
                        debug!("Error on recreating subscriptions {}", err);
                        panic!("Abort during reconnection");
                    };
                }
            }
        }
    }

    /// Collect the IBC events from the subscriptions
    pub async fn collect_events(&mut self) -> Result<(), TMError> {
        if let Some(event) = select_all(&mut self.subscriptions).next().await {
            match event {
                Ok(event) => {
                    if let Ok(ibc_events) = ibc::events::get_all_events(event) {
                        // TODO - send_timeout()?
                        self.channel_to_handler
                            .send((self.chain_id, ibc_events))
                            .await?;
                    }
                }
                Err(_e) => (), // TODO,
            }
        }

        Ok(())
    }
}
