use core::fmt;
use core::mem;
use crossbeam_channel::Sender;
use serde::Deserialize;
use serde::Serialize;
use tracing::{debug, trace};

use ibc::{
    core::{ics02_client::events::NewBlock, ics24_host::identifier::ChainId},
    events::IbcEvent,
    Height,
};

use crate::util::lock::{LockExt, RwArc};
use crate::util::task::TaskHandle;
use crate::{event::monitor::EventBatch, object::Object};

use super::{WorkerCmd, WorkerId};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WorkerData {
    Client { misbehaviour: bool, refresh: bool },
}

pub struct WorkerHandle {
    id: WorkerId,
    object: Object,
    data: Option<WorkerData>,
    tx: RwArc<Option<Sender<WorkerCmd>>>,
    task_handles: Vec<TaskHandle>,
}

impl WorkerHandle {
    pub fn new(
        id: WorkerId,
        object: Object,
        data: Option<WorkerData>,
        tx: Option<Sender<WorkerCmd>>,
        task_handles: Vec<TaskHandle>,
    ) -> Self {
        Self {
            id,
            object,
            data,
            tx: <RwArc<_>>::new_lock(tx),
            task_handles,
        }
    }

    pub fn try_send_command(&self, cmd: WorkerCmd) {
        let res = if let Some(tx) = self.tx.acquire_read().as_ref() {
            tx.send(cmd)
        } else {
            Ok(())
        };

        if res.is_err() {
            debug!("dropping sender end for worker {} as the receiver was dropped when the worker task terminated", self.id);
            *self.tx.acquire_write() = None;
        }
    }

    /// Send a batch of events to the worker.
    pub fn send_events(&self, height: Height, events: Vec<IbcEvent>, chain_id: ChainId) {
        let batch = EventBatch {
            chain_id,
            height,
            events,
        };

        self.try_send_command(WorkerCmd::IbcEvents { batch });
    }

    /// Send a batch of [`NewBlock`] event to the worker.
    pub fn send_new_block(&self, height: Height, new_block: NewBlock) {
        self.try_send_command(WorkerCmd::NewBlock { height, new_block });
    }

    /// Instruct the worker to clear pending packets.
    pub fn clear_pending_packets(&self) {
        self.try_send_command(WorkerCmd::ClearPendingPackets);
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

    /// Get a reference to the worker handle's data.
    pub fn data(&self) -> Option<&WorkerData> {
        self.data.as_ref()
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
