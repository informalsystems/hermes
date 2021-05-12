use std::fmt;

use tracing::{debug, error, info};

use crate::{chain::handle::ChainHandlePair, object::Object};

mod handle;
pub use handle::WorkerHandle;

mod cmd;
pub use cmd::WorkerCmd;

mod client;
pub use client::ClientWorker;

mod uni_chan_path;
pub use uni_chan_path::UniChanPathWorker;

/// A worker processes batches of events associated with a given [`Object`].
pub enum Worker {
    Client(ClientWorker),
    UniChanPath(UniChanPathWorker),
}

impl fmt::Display for Worker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} <-> {}]", self.chains().a.id(), self.chains().b.id(),)
    }
}

impl Worker {
    /// Spawn a worker which relay events pertaining to an [`Object`] between two `chains`.
    pub fn spawn(chains: ChainHandlePair, object: Object) -> WorkerHandle {
        let (tx, rx) = crossbeam_channel::unbounded();

        debug!(
            "[{}] spawned worker with chains a:{} and b:{} for object {:#?} ",
            object.short_name(),
            chains.a.id(),
            chains.b.id(),
            object,
        );

        let worker = match object {
            Object::Client(client) => Self::Client(ClientWorker::new(chains, rx, client)),
            Object::UnidirectionalChannelPath(path) => {
                Self::UniChanPath(UniChanPathWorker::new(chains, rx, path))
            }
        };

        let thread_handle = std::thread::spawn(move || worker.run());
        WorkerHandle::new(tx, thread_handle)
    }

    /// Run the worker event loop.
    fn run(self) {
        let result = match self {
            Self::Client(w) => w.run(),
            Self::UniChanPath(w) => w.run(),
        };

        if let Err(e) = result {
            error!("worker error: {}", e);
        }

        info!("worker exits");
    }

    fn chains(&self) -> &ChainHandlePair {
        match self {
            Self::Client(w) => &w.chains(),
            Self::UniChanPath(w) => w.chains(),
        }
    }
}
