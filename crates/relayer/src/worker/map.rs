use alloc::collections::btree_map::BTreeMap as HashMap;
use core::mem;

use ibc_relayer_types::core::ics02_client::events::NewBlock;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::Height;
use tracing::{debug, trace};

use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    config::Config,
    object::Object,
    telemetry,
};

use super::{spawn_worker_tasks, WorkerHandle, WorkerId};

/// Manage the lifecycle of [`WorkerHandle`]s associated with [`Object`]s.
#[derive(Debug)]
pub struct WorkerMap {
    workers: HashMap<Object, WorkerHandle>,
    latest_worker_id: WorkerId,
}

impl Default for WorkerMap {
    fn default() -> Self {
        Self {
            workers: HashMap::new(),
            latest_worker_id: WorkerId::new(0),
        }
    }
}

impl WorkerMap {
    /// Create a new worker map, which will spawn workers with
    /// the given channel for sending messages back to the
    /// [supervisor](crate::supervisor::SupervisorHandle).
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `true` if there is a spawned [`WorkerHandle`] associated with the given [`Object`].
    pub fn contains(&self, object: &Object) -> bool {
        self.workers.contains_key(object)
    }

    /// Remove the [`WorkerHandle`] associated with the given [`Object`] from
    /// the map and wait for its thread to terminate.
    pub fn remove_stopped(&mut self, id: WorkerId, object: Object) -> bool {
        match self.workers.remove(&object) {
            Some(handle) if handle.id() == id => {
                telemetry!(worker, metric_type(&object), -1);

                let id = handle.id();

                trace!(
                    worker.id = %id, worker.object = %object.short_name(),
                    "waiting for worker loop to end"
                );

                handle.join();

                trace!(
                    worker.id = %id, worker.object = %object.short_name(),
                    "worker loop has ended"
                );

                true
            }
            Some(handle) => {
                debug!(
                    worker.object = %object.short_name(),
                    "ignoring attempt to remove worker with outdated id {} (current: {})",
                    id, handle.id()
                );

                self.workers.insert(object, handle);

                false
            }
            None => {
                debug!(
                    worker.object = %object.short_name(),
                    "ignoring attempt to remove unknown worker",
                );

                false
            }
        }
    }

    /// Returns all the [`WorkerHandle`] which are interested in new block events originating
    /// from the chain with the given [`ChainId`].
    /// See: [`Object::notify_new_block`]
    pub fn to_notify<'a>(
        &'a self,
        src_chain_id: &'a ChainId,
    ) -> impl Iterator<Item = &'a WorkerHandle> {
        self.workers.iter().filter_map(move |(o, w)| {
            if !w.is_stopped() && o.notify_new_block(src_chain_id) {
                Some(w)
            } else {
                None
            }
        })
    }

    pub fn notify_new_block(&self, src_chain_id: &ChainId, height: Height, new_block: NewBlock) {
        for worker in self.to_notify(src_chain_id) {
            // Ignore send error if the worker task handling
            // NewBlock cmd has been terminated.
            worker.send_new_block(height, new_block);
        }
    }

    /// Get a handle to the worker in charge of handling events associated
    /// with the given [`Object`].
    ///
    /// This function will spawn a new [`WorkerHandle`] if one does not exists already.
    pub fn get_or_spawn<Chain: ChainHandle>(
        &mut self,
        object: Object,
        src: Chain,
        dst: Chain,
        config: &Config,
    ) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let worker = self.spawn_worker(src, dst, &object, config);
            self.workers.entry(object).or_insert(worker)
        }
    }

    /// Spawn a new [`WorkerHandle`], only if one does not exists already.
    ///
    /// Returns whether or not the worker was actually spawned.
    pub fn spawn<Chain: ChainHandle>(
        &mut self,
        src: Chain,
        dst: Chain,
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
    fn spawn_worker<Chain: ChainHandle>(
        &mut self,
        src: Chain,
        dst: Chain,
        object: &Object,
        config: &Config,
    ) -> WorkerHandle {
        telemetry!(worker, metric_type(object), 1);

        spawn_worker_tasks(
            ChainHandlePair { a: src, b: dst },
            self.next_worker_id(),
            object.clone(),
            config,
        )
    }

    /// Compute the next worker id
    fn next_worker_id(&mut self) -> WorkerId {
        let id = self.latest_worker_id.next();
        self.latest_worker_id = id;
        id
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

    /// List the [`WorkerHandle`]s associated with the given chain.
    pub fn workers_for_chain(&self, chain_id: &ChainId) -> Vec<&WorkerHandle> {
        self.workers
            .iter()
            .filter_map(|(o, h)| o.for_chain(chain_id).then_some(h))
            .collect()
    }

    /// Return all the handles to the workers tracked in this map.
    pub fn handles(&self) -> impl Iterator<Item = &WorkerHandle> {
        self.workers.values()
    }

    /// Shutdown the worker associated with the given [`Object`], synchronously.
    pub fn shutdown_worker(&mut self, object: &Object) {
        if let Some(handle) = self.workers.remove(object) {
            telemetry!(worker, metric_type(object), -1);

            handle.shutdown_and_wait();
        }
        // Drop handle automatically handles the waiting for tasks to terminate.
    }

    /// Shut down all the workers, asynchronously.
    pub fn shutdown(&mut self) {
        let workers = mem::take(&mut self.workers);
        for worker in workers.values() {
            // Send shutdown signal to all tasks in parallel.
            worker.shutdown();
        }
    }
}

// Drop handle to send shutdown signals to background tasks in parallel
// before waiting for all of them to terminate.
impl Drop for WorkerMap {
    fn drop(&mut self) {
        self.shutdown()
    }
}

#[cfg(feature = "telemetry")]
fn metric_type(o: &Object) -> ibc_telemetry::state::WorkerType {
    use ibc_telemetry::state::WorkerType;

    match o {
        Object::Client(_) => WorkerType::Client,
        Object::Connection(_) => WorkerType::Connection,
        Object::Channel(_) => WorkerType::Channel,
        Object::Packet(_) => WorkerType::Packet,
        Object::Wallet(_) => WorkerType::Wallet,
    }
}
