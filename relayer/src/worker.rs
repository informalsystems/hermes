use std::fmt;

use crossbeam_channel::Sender;
use tracing::{debug, error, info};

use crate::{chain::handle::ChainHandlePair, object::Object, telemetry::TelemetryHandle};

pub mod retry_strategy;

mod handle;
pub use handle::WorkerHandle;

mod cmd;
pub use cmd::WorkerCmd;

mod map;
pub use map::WorkerMap;

mod client;
pub use client::ClientWorker;

mod channel;
pub use channel::ChannelWorker;

mod uni_chan_path;
pub use uni_chan_path::UniChanPathWorker;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkerMsg {
    Stopped(Object),
}

/// A worker processes batches of events associated with a given [`Object`].
pub enum Worker {
    Client(ClientWorker),
    Channel(ChannelWorker),
    UniChanPath(UniChanPathWorker),
}

impl fmt::Display for Worker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} <-> {}]", self.chains().a.id(), self.chains().b.id(),)
    }
}

impl Worker {
    /// Spawn a worker which relay events pertaining to an [`Object`] between two `chains`.
    pub fn spawn(
        chains: ChainHandlePair,
        object: Object,
        msg_tx: Sender<WorkerMsg>,
        telemetry: TelemetryHandle,
    ) -> WorkerHandle {
        let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();

        debug!(
            "[{}] spawned worker with chains a:{} and b:{} for object {:#?} ",
            object.short_name(),
            chains.a.id(),
            chains.b.id(),
            object,
        );

        let worker = match object {
            Object::Client(client) => {
                Self::Client(ClientWorker::new(client, chains, cmd_rx, telemetry))
            }
            Object::Channel(channel) => {
                Self::Channel(ChannelWorker::new(channel, chains, cmd_rx, telemetry))
            }
            Object::UnidirectionalChannelPath(path) => {
                Self::UniChanPath(UniChanPathWorker::new(path, chains, cmd_rx, telemetry))
            }
        };

        let thread_handle = std::thread::spawn(move || worker.run(msg_tx));
        WorkerHandle::new(cmd_tx, thread_handle)
    }

    /// Run the worker event loop.
    fn run(self, msg_tx: Sender<WorkerMsg>) {
        let object = self.object();

        let result = match self {
            Self::Client(w) => w.run(),
            Self::Channel(w) => w.run(),
            Self::UniChanPath(w) => w.run(),
        };

        if let Err(e) = result {
            error!("worker error: {}", e);
        }

        if let Err(e) = msg_tx.send(WorkerMsg::Stopped(object)) {
            error!("failed to notify supervisor that worker stopped: {}", e);
        }

        info!("worker stopped");
    }

    fn chains(&self) -> &ChainHandlePair {
        match self {
            Self::Client(w) => &w.chains(),
            Self::Channel(w) => w.chains(),
            Self::UniChanPath(w) => w.chains(),
        }
    }

    fn object(&self) -> Object {
        match self {
            Worker::Client(w) => w.object().clone().into(),
            Worker::Channel(w) => w.object().clone().into(),
            Worker::UniChanPath(w) => w.object().clone().into(),
        }
    }
}
