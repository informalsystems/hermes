use std::{
    fmt,
    thread::{self, JoinHandle},
};

use crossbeam_channel::Sender;
use tracing::trace;

use ibc::{
    events::IbcEvent, ics02_client::events::NewBlock, ics24_host::identifier::ChainId, Height,
};

use crate::event::monitor::EventBatch;

use super::WorkerCmd;

/// Handle to a [`Worker`], for sending [`WorkerCmd`]s to it.
pub struct WorkerHandle {
    tx: Sender<WorkerCmd>,
    thread_handle: JoinHandle<()>,
}

impl fmt::Debug for WorkerHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WorkerHandle").finish()
    }
}

impl WorkerHandle {
    pub fn new(tx: Sender<WorkerCmd>, thread_handle: JoinHandle<()>) -> Self {
        Self { tx, thread_handle }
    }

    /// Send a batch of events to the worker.
    pub fn send_events(
        &self,
        height: Height,
        events: Vec<IbcEvent>,
        chain_id: ChainId,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let batch = EventBatch {
            chain_id,
            height,
            events,
        };

        trace!("supervisor sends {:?}", batch);
        self.tx.send(WorkerCmd::IbcEvents { batch })?;
        Ok(())
    }

    /// Send a batch of [`NewBlock`] event to the worker.
    pub fn send_new_block(
        &self,
        height: Height,
        new_block: NewBlock,
    ) -> Result<(), Box<dyn std::error::Error>> {
        self.tx.send(WorkerCmd::NewBlock { height, new_block })?;
        Ok(())
    }

    /// Wait for the worker thread to finish.
    pub fn join(self) -> thread::Result<()> {
        self.thread_handle.join()
    }
}
