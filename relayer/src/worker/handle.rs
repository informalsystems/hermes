use std::{
    fmt,
    thread::{self, JoinHandle},
};

use anomaly::BoxError;
use crossbeam_channel::Sender;
use tracing::trace;

use ibc::{
    events::IbcEvent, ics02_client::events::NewBlock, ics24_host::identifier::ChainId, Height,
};

use crate::{event::monitor::EventBatch, object::Object};

use super::{WorkerCmd, WorkerId};

/// Handle to a [`Worker`], for sending [`WorkerCmd`]s to it.
pub struct WorkerHandle {
    id: WorkerId,
    object: Object,
    tx: Sender<WorkerCmd>,
    thread_handle: JoinHandle<()>,
}

impl fmt::Debug for WorkerHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WorkerHandle")
            .field("id", &self.id)
            .field("object", &self.object)
            .finish_non_exhaustive()
    }
}

impl WorkerHandle {
    pub fn new(
        id: WorkerId,
        object: Object,
        tx: Sender<WorkerCmd>,
        thread_handle: JoinHandle<()>,
    ) -> Self {
        Self {
            id,
            object,
            tx,
            thread_handle,
        }
    }

    /// Send a batch of events to the worker.
    pub fn send_events(
        &self,
        height: Height,
        events: Vec<IbcEvent>,
        chain_id: ChainId,
    ) -> Result<(), BoxError> {
        let batch = EventBatch {
            chain_id,
            height,
            events,
        };

        self.tx.send(WorkerCmd::IbcEvents { batch })?;
        Ok(())
    }

    /// Send a [`NewBlock`] event to the worker.
    pub fn send_new_block(&self, height: Height, new_block: NewBlock) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd::NewBlock { height, new_block })?;
        Ok(())
    }

    /// Shutdown the worker.
    pub fn shutdown(&self) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd::Shutdown)?;
        Ok(())
    }

    /// Wait for the worker thread to finish.
    pub fn join(self) -> thread::Result<()> {
        trace!(worker = %self.object.short_name(), "worker::handle: waiting for worker loop to end");
        let res = self.thread_handle.join();
        trace!(worker = %self.object.short_name(), "worker::handle: waiting for worker loop to end: done");
        res
    }

    /// Get the worker's id.
    pub fn id(&self) -> WorkerId {
        self.id
    }

    /// Get a reference to the worker's object.
    pub fn object(&self) -> &Object {
        &self.object
    }
}
