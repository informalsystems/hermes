use relayer_modules::events::IBCEvent;
use tendermint::{net, Error as TMError};
use tendermint_rpc::{event_listener, event_listener::EventSubscription};
use tokio::sync::mpsc::Sender;

use ::tendermint::chain::Id as ChainId;
use tracing::{debug, info};

/// Connect to a TM node, receive push events over a websocket and filter them for the
/// event handler.
pub struct EventMonitor {
    chain_id: ChainId,
    /// Websocket to collect events from
    event_listener: event_listener::EventListener,
    /// Channel to handler where the monitor for this chain sends the events
    channel_to_handler: Sender<(ChainId, Vec<IBCEvent>)>,
    /// Node Address
    node_addr: net::Address,
    /// Queries
    event_queries: Vec<EventSubscription>,
}

impl EventMonitor {
    /// Create an event monitor, connect to a node and subscribe to queries.
    pub async fn create(
        chain_id: ChainId,
        rpc_addr: net::Address,
        channel_to_handler: Sender<(ChainId, Vec<IBCEvent>)>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let mut event_listener = event_listener::EventListener::connect(rpc_addr.clone()).await?;
        // TODO move them to config file(?)
        let event_queries = vec![
            EventSubscription::TransactionSubscription,
            EventSubscription::BlockSubscription,
        ];
        for query in event_queries.clone() {
            event_listener.subscribe(query.clone()).await?;
        }
        Ok(EventMonitor {
            chain_id,
            event_listener,
            channel_to_handler,
            node_addr: rpc_addr.clone(),
            event_queries,
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
                    match event_listener::EventListener::connect(self.node_addr.clone()).await {
                        Ok(event_listener) => {
                            debug!("Reconnected");
                            self.event_listener = event_listener;
                            for query in &self.event_queries {
                                match self.event_listener.subscribe((*query).clone()).await {
                                    Ok(..) => continue,
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
        if let Some(tm_event) = self.event_listener.get_event().await? {
            if let Ok(ibc_events) = relayer_modules::events::get_all_events(tm_event) {
                // TODO - send_timeout()?
                self.channel_to_handler
                    .send((self.chain_id, ibc_events))
                    .await?;
            }
        }
        Ok(())
    }
}
