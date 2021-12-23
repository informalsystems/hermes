use core::fmt;
use core::mem;
use crossbeam_channel::Sender;
use tracing::trace;

use ibc::{
    core::{ics02_client::events::NewBlock, ics24_host::identifier::ChainId},
    events::IbcEvent,
    Height,
};

use crate::util::task::TaskHandle;
use crate::{event::monitor::EventBatch, object::Object};

use super::error::WorkerError;
use super::{WorkerCmd, WorkerId};

pub struct WorkerHandle {
    id: WorkerId,
    object: Object,
    tx: Sender<WorkerCmd>,
    task_handles: Vec<TaskHandle>,
}

impl WorkerHandle {
    pub fn new(
        id: WorkerId,
        object: Object,
        tx: Sender<WorkerCmd>,
        task_handles: Vec<TaskHandle>,
    ) -> Self {
        Self {
            id,
            object,
            tx,
            task_handles,
        }
    }

    /// Send a batch of events to the worker.
    pub fn send_events(
        &self,
        height: Height,
        events: Vec<IbcEvent>,
        chain_id: ChainId,
    ) -> Result<(), WorkerError> {
        let batch = EventBatch {
            chain_id,
            height,
            events,
        };

        self.tx
            .send(WorkerCmd::IbcEvents { batch })
            .map_err(WorkerError::send)
    }

    /// Send a batch of [`NewBlock`] event to the worker.
    pub fn send_new_block(&self, height: Height, new_block: NewBlock) -> Result<(), WorkerError> {
        self.tx
            .send(WorkerCmd::NewBlock { height, new_block })
            .map_err(WorkerError::send)
    }

    /// Instruct the worker to clear pending packets.
    pub fn clear_pending_packets(&self) -> Result<(), WorkerError> {
        self.tx
            .send(WorkerCmd::ClearPendingPackets)
            .map_err(WorkerError::send)
    }

    /// Shutdown all worker tasks without waiting for them to terminate.
    pub fn shutdown(&self) {
        for task in self.task_handles.iter() {
            task.shutdown()
        }
    }

    /// Shutdown all worker tasks and wait for them to terminate
    pub fn shutdown_and_wait(self) {
        for task in self.task_handles.iter() {
            // Send shutdown signal to all tasks in parallel.
            task.shutdown()
        }
        // Drop handle automatically handles the waiting for tasks to terminate.
    }

    pub fn is_stopped(&self) -> bool {
        for task in self.task_handles.iter() {
            if !task.is_stopped() {
                return false;
            }
        }
        true
    }

    /// Wait for the worker thread to finish.
    pub fn join(mut self) {
        let task_handles = mem::take(&mut self.task_handles);
        trace!(worker = %self.object.short_name(), "worker::handle: waiting for worker loop to end");
        for task in task_handles.into_iter() {
            task.join()
        }
        trace!(worker = %self.object.short_name(), "worker::handle: waiting for worker loop to end: done");
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

// Drop handle to send shutdown signals to background tasks in parallel
// before waiting for all of them to terminate.
impl Drop for WorkerHandle {
    fn drop(&mut self) {
        self.shutdown()
    }
}

impl fmt::Debug for WorkerHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WorkerHandle")
            .field("id", &self.id)
            .field("object", &self.object)
            .finish_non_exhaustive()
    }
}
