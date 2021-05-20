use std::collections::HashMap;

use crossbeam_channel::Sender;
use ibc::ics24_host::identifier::ChainId;

use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    object::Object,
};

use super::{Worker, WorkerHandle, WorkerMsg};

/// Manage the lifecycle of [`Worker`]s associated with [`Object`]s.
#[derive(Debug)]
pub struct WorkerMap {
    workers: HashMap<Object, WorkerHandle>,
    msg_tx: Sender<WorkerMsg>,
}

impl WorkerMap {
    /// Create a new worker map, which will spawn workers with
    /// the given channel for sending messages back to the [`Supervisor`].
    pub fn new(msg_tx: Sender<WorkerMsg>) -> Self {
        Self {
            workers: HashMap::new(),
            msg_tx,
        }
    }

    /// Returns `true` if there is a spawned [`Worker`] associated with the given [`Object`].
    pub fn contains(&self, object: &Object) -> bool {
        self.workers.contains_key(object)
    }

    /// Remove the [`Worker`] associated with the given [`Object`] from
    /// the map and wait for its thread to terminate.
    pub fn remove_stopped(&mut self, object: &Object) -> bool {
        if let Some(handle) = self.workers.remove(object) {
            let _ = handle.join();
            true
        } else {
            false
        }
    }

    /// Returns all the [`Worker`] which are interested in new block events originating
    /// from the chain with the given [`ChainId`].
    /// See: [`Object::notify_new_block`]
    pub fn to_notify<'a>(
        &'a self,
        src_chain_id: &'a ChainId,
    ) -> impl Iterator<Item = &'a WorkerHandle> {
        self.workers.iter().filter_map(move |(o, w)| {
            if o.notify_new_block(src_chain_id) {
                Some(w)
            } else {
                None
            }
        })
    }

    /// Get a handle to the worker in charge of handling events associated
    /// with the given [`Object`].
    ///
    /// This function will spawn a new [`Worker`] if one does not exists already.
    pub fn get_or_spawn(
        &mut self,
        object: Object,
        src: Box<dyn ChainHandle>,
        dst: Box<dyn ChainHandle>,
    ) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let handles = ChainHandlePair { a: src, b: dst };
            let worker = Worker::spawn(handles, object.clone(), self.msg_tx.clone());
            self.workers.entry(object).or_insert(worker)
        }
    }
}
