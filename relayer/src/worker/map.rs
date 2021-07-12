use std::collections::HashMap;

use crossbeam_channel::Sender;

use ibc::ics24_host::identifier::ChainId;
use tracing::{debug, warn};

use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    config::Config,
    object::Object,
    telemetry,
    telemetry::Telemetry,
};

use super::{Worker, WorkerHandle, WorkerMsg};

/// Manage the lifecycle of [`Worker`]s associated with [`Object`]s.
#[derive(Debug)]
pub struct WorkerMap {
    workers: HashMap<Object, WorkerHandle>,
    msg_tx: Sender<WorkerMsg>,
    telemetry: Telemetry,
}

impl WorkerMap {
    /// Create a new worker map, which will spawn workers with
    /// the given channel for sending messages back to the [`Supervisor`].
    pub fn new(msg_tx: Sender<WorkerMsg>, telemetry: Telemetry) -> Self {
        Self {
            workers: HashMap::new(),
            msg_tx,
            telemetry,
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
            telemetry!(self.telemetry.worker(metric_type(object), -1));
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
        config: &Config,
    ) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let worker = self.spawn_worker(src, dst, &object, config);
            self.workers.entry(object).or_insert(worker)
        }
    }

    /// Spawn a new [`Worker`], only if one does not exists already.
    ///
    /// Returns whether or not the worker was actually spawned.
    pub fn spawn(
        &mut self,
        src: Box<dyn ChainHandle>,
        dst: Box<dyn ChainHandle>,
        object: &Object,
        config: &Config,
    ) -> bool {
        if !self.workers.contains_key(object) {
            let worker = self.spawn_worker(src, dst, object, config);
            self.workers.entry(object.clone()).or_insert(worker);
            true
        } else {
            false
        }
    }

    /// Force spawn a worker for the given [`Object`].
    fn spawn_worker(
        &mut self,
        src: Box<dyn ChainHandle>,
        dst: Box<dyn ChainHandle>,
        object: &Object,
        config: &Config,
    ) -> WorkerHandle {
        telemetry!(self.telemetry.worker(metric_type(object), 1));

        Worker::spawn(
            ChainHandlePair { a: src, b: dst },
            object.clone(),
            self.msg_tx.clone(),
            self.telemetry.clone(),
            config,
        )
    }

    /// List the [`Object`]s for which there is an associated worker
    /// for the given chain.
    pub fn objects_for_chain(&self, chain_id: &ChainId) -> Vec<Object> {
        self.workers
            .keys()
            .filter(|o| o.for_chain(chain_id))
            .cloned()
            .collect()
    }

    /// Shutdown the worker associated with the given [`Object`].
    pub fn shutdown_worker(&mut self, object: &Object) {
        if let Some(handle) = self.workers.remove(object) {
            telemetry!(self.telemetry.worker(metric_type(object), -1));

            match handle.shutdown() {
                Ok(()) => {
                    debug!(object = %object.short_name(), "waiting for worker to exit");
                    let _ = handle.join();
                }
                Err(e) => {
                    warn!(object = %object.short_name(), "a worker may have failed to shutdown properly: {}", e);
                }
            }
        }
    }

    /// Get an iterator over the worker map's objects.
    pub fn objects(&self) -> impl Iterator<Item = &Object> {
        self.workers.keys()
    }
}

#[cfg(feature = "telemetry")]
fn metric_type(o: &Object) -> ibc_telemetry::state::WorkerType {
    use ibc_telemetry::state::WorkerType::*;
    match o {
        Object::Client(_) => Client,
        Object::Connection(_) => Connection,
        Object::Channel(_) => Channel,
        Object::Packet(_) => Packet,
    }
}
