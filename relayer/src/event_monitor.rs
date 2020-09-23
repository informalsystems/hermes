use ibc::events::IBCEvent;
use tendermint::{net, Error as TMError};
use tendermint_rpc::Subscription;
use tendermint_rpc::{SubscriptionClient, WebSocketClient};
use tokio::stream::StreamExt;
use tokio::sync::mpsc::Sender;

use ::tendermint::chain::Id as ChainId;
use tracing::{debug, info};

/// Connect to a TM node, receive push events over a websocket and filter them for the
/// event handler.
pub struct EventMonitor {
    chain_id: ChainId,
    /// Websocket to collect events from
    websocket_client: WebSocketClient,
    /// Channel to handler where the monitor for this chain sends the events
    channel_to_handler: Sender<(ChainId, Vec<IBCEvent>)>,
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
        chain_id: ChainId,
        rpc_addr: net::Address,
        channel_to_handler: Sender<(ChainId, Vec<IBCEvent>)>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let mut websocket_client = WebSocketClient::new(rpc_addr.clone()).await?;
        let mut subscriptions = vec![];

        // TODO move them to config file(?)
        let event_queries = vec![
            "tm.event='NewTx'".to_string(),
            "tm.event='NewBlock'".to_string(),
        ];

        for query in &event_queries {
            let subscription = websocket_client.subscribe(query.clone()).await?;
            subscriptions.push(subscription);
        }

        Ok(EventMonitor {
            chain_id,
            websocket_client,
            channel_to_handler,
            node_addr: rpc_addr.clone(),
            event_queries,
            subscriptions,
        })
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
                    match WebSocketClient::new(self.node_addr.clone()).await {
                        Ok(websocket_client) => {
                            debug!("Reconnected");

                            self.websocket_client = websocket_client;
                            self.subscriptions.clear();

                            for query in &self.event_queries {
                                match self.websocket_client.subscribe(query.clone()).await {
                                    Ok(subscription) => {
                                        self.subscriptions.push(subscription);
                                    }
                                    Err(err) => {
                                        debug!("Error on recreating subscriptions {}", err);
                                        panic!("Abort during reconnection");
                                    }
                                };
                            }
                        }
                        Err(err) => {
                            debug!("Error on reconnection {}", err);
                            panic!("Abort on failed reconnection")
                        }
                    }
                }
            }
        }
    }

    /// get a TM event and extract the IBC events
    pub async fn collect_events(&mut self) -> Result<(), TMError> {
        for subscription in &mut self.subscriptions {
            if let Some(event) = subscription.next().await {
                if let Ok(event) = event {
                    if let Ok(ibc_events) = ibc::events::get_all_events(event) {
                        // TODO - send_timeout()?
                        self.channel_to_handler
                            .send((self.chain_id, ibc_events))
                            .await?;
                    }
                }
            }
        }

        Ok(())
    }
}
