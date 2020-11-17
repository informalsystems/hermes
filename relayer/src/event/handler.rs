use crossbeam_channel as channel;
use ibc::events::IBCEvent;
use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tracing::{debug, info};

use crate::event::monitor::EventBatch;

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler {
    rx_batch: channel::Receiver<EventBatch>,
    relay: bool,
}

impl EventHandler {
    /// Constructor for the Event Handler
    pub fn new(rx_batch: channel::Receiver<EventBatch>, relay: bool) -> Self {
        Self { rx_batch, relay }
    }

    ///Event Handler loop
    pub fn run(&mut self) {
        info!("running IBC Event Handler");

        while let Ok(batch) = self.rx_batch.recv() {
            let chain_id = batch.chain_id.into();
            for event in batch.events {
                self.handle(&chain_id, batch.height, event);
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
