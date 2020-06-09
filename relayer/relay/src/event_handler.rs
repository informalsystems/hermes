use relayer_modules::events::IBCEvent;
use tokio::sync::mpsc::Receiver;

use ::tendermint::chain::Id as ChainId;
use tracing::{debug, info};

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler {
    channel_from_monitors: Receiver<(ChainId, Vec<IBCEvent>)>,
}

impl EventHandler {
    /// Constructor for the Event Handler
    pub fn new(channel_from_monitors: Receiver<(ChainId, Vec<IBCEvent>)>) -> Self {
        Self {
            channel_from_monitors,
        }
    }

    ///Event Handler loop
    pub async fn run(&mut self) {
        info!("running IBC Event Handler");

        loop {
            if let Some(events) = self.channel_from_monitors.recv().await {
                for event in events.1 {
                    self.handle(events.0, event);
                }
            }
        }
    }

    fn handle(&self, id: ChainId, event: IBCEvent) {
        debug!("Relayer handle event from {}: {}", id, event.to_json());
    }
}
