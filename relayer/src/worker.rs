use std::fmt;

use crossbeam_channel::Sender;
use tracing::{debug, error, info};

use crate::{chain::handle::ChainHandlePair, object::Object, telemetry::Telemetry};

pub mod retry_strategy;

mod handle;
pub use handle::WorkerHandle;

mod cmd;
pub use cmd::WorkerCmd;

mod map;
pub use map::WorkerMap;

mod client;
pub use client::ClientWorker;

mod connection;
pub use connection::ConnectionWorker;

mod channel;
pub use channel::ChannelWorker;

mod uni_chan_path;
pub use uni_chan_path::PacketWorker;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkerMsg {
    Stopped(Object),
}

/// A worker processes batches of events associated with a given [`Object`].
pub enum Worker {
    Client(ClientWorker),
    Connection(ConnectionWorker),
    Channel(ChannelWorker),
    UniChanPath(PacketWorker),
}

impl fmt::Display for Worker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} <-> {}]", self.chains().a.id(), self.chains().b.id(),)
    }
}

impl Worker {
    /// Spawn a worker which relays events pertaining to an [`Object`] between two `chains`.
    pub fn spawn(
        chains: ChainHandlePair,
        object: Object,
        msg_tx: Sender<WorkerMsg>,
        telemetry: Telemetry,
    ) -> WorkerHandle {
        let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();

        debug!("spawning worker for object {}", object.short_name(),);

        let worker = match object {
            Object::Client(client) => {
                Self::Client(ClientWorker::new(client, chains, cmd_rx, telemetry))
            }
            Object::Connection(connection) => {
                Self::Connection(ConnectionWorker::new(connection, chains, cmd_rx, telemetry))
            }
            Object::Channel(channel) => {
                Self::Channel(ChannelWorker::new(channel, chains, cmd_rx, telemetry))
            }
            Object::Packet(path) => {
                Self::UniChanPath(PacketWorker::new(path, chains, cmd_rx, telemetry))
            }
        };

        let thread_handle = std::thread::spawn(move || worker.run(msg_tx));
        WorkerHandle::new(cmd_tx, thread_handle)
    }

    /// Run the worker event loop.
    fn run(self, msg_tx: Sender<WorkerMsg>) {
        let object = self.object();
        let name = object.short_name();

        let result = match self {
            Self::Client(w) => w.run(),
            Self::Connection(w) => w.run(),
            Self::Channel(w) => w.run(),
            Self::UniChanPath(w) => w.run(),
        };

        if let Err(e) = result {
            error!("[{}] worker aborted with error: {}", name, e);
        }

        if let Err(e) = msg_tx.send(WorkerMsg::Stopped(object)) {
            error!(
                "[{}] failed to notify supervisor that worker stopped: {}",
                name, e
            );
        }

        info!("[{}] worker stopped", name);
    }

    fn chains(&self) -> &ChainHandlePair {
        match self {
            Self::Client(w) => &w.chains(),
            Self::Connection(w) => w.chains(),
            Self::Channel(w) => w.chains(),
            Self::UniChanPath(w) => w.chains(),
        }
    }

    fn object(&self) -> Object {
        match self {
            Worker::Client(w) => w.object().clone().into(),
            Worker::Connection(w) => w.object().clone().into(),
            Worker::Channel(w) => w.object().clone().into(),
            Worker::UniChanPath(w) => w.object().clone().into(),
        }
    }
}
