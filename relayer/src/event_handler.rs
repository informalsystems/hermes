use ibc::events::IBCEvent;
use tendermint::block::Height;
use tokio::sync::mpsc::Receiver;

use ::tendermint::chain::Id as ChainId;
use tracing::{debug, info};

use crate::event_monitor::EventBatch;

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler {
    channel_from_monitors: Receiver<EventBatch>,
    relay: bool,
}

impl EventHandler {
    /// Constructor for the Event Handler
    pub fn new(channel_from_monitors: Receiver<EventBatch>, relay: bool) -> Self {
        Self {
            channel_from_monitors,
            relay,
        }
    }

    ///Event Handler loop
    pub async fn run(&mut self) {
        info!("running IBC Event Handler");

        loop {
            if let Some(batch) = self.channel_from_monitors.recv().await {
                for event in batch.events {
                    self.handle(&batch.chain_id, batch.height, event);
                }
            }
        }
    }

    fn handle(&self, id: &ChainId, height: Height, event: IBCEvent) {
        if !self.relay {
            info!(
                "Chain {} pushed an event at height {}: {}",
                id,
                height,
                event.to_json()
            );

            return;
        }

        // TODO - main event handler
        debug!(
            "Relayer handle event from {} at height {}: {}",
            id,
            height,
            event.to_json()
        );
    }
}
