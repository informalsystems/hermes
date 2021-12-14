use alloc::sync::Arc;
use core::fmt;
use serde::{Deserialize, Serialize};

use crate::foreign_client::ForeignClient;
use crate::link::{Link, LinkParameters};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    config::Config,
    object::Object,
};

pub mod retry_strategy;

mod error;
pub use error::{RunError, WorkerError};

mod handle;
pub use handle::WorkerHandle;

mod cmd;
pub use cmd::WorkerCmd;

mod map;
pub use map::WorkerMap;

pub mod client;

pub mod connection;

pub mod channel;

pub mod packet;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct WorkerId(u64);

impl WorkerId {
    pub fn new(id: u64) -> Self {
        Self(id)
    }

    pub fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

impl fmt::Display for WorkerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn spawn_worker_tasks<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: ChainHandlePair<ChainA, ChainB>,
    id: WorkerId,
    object: Object,
    config: &Config,
) -> WorkerHandle {
    let mut task_handles = Vec::new();
    let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();

    match &object {
        Object::Client(client) => {
            let client = ForeignClient::restore(client.dst_client_id.clone(), chains.b, chains.a);

            let refresh_task = client::spawn_refresh_client(client.clone());
            if let Some(refresh_task) = refresh_task {
                task_handles.push(refresh_task);
            }

            let misbehavior_task = client::detect_misbehavior_task(cmd_rx, client);
            if let Some(task) = misbehavior_task {
                task_handles.push(task);
            }
        }
        Object::Connection(connection) => {
            let connection_task =
                connection::spawn_connection_worker(connection.clone(), chains, cmd_rx);
            task_handles.push(connection_task);
        }
        Object::Channel(channel) => {
            let channel_task = channel::spawn_channel_worker(channel.clone(), chains, cmd_rx);
            task_handles.push(channel_task);
        }
        Object::Packet(path) => {
            let packets_config = config.mode.packets;
            let link = Link::new_from_opts(
                chains.a.clone(),
                chains.b,
                LinkParameters {
                    src_port_id: path.src_port_id.clone(),
                    src_channel_id: path.src_channel_id.clone(),
                },
                packets_config.tx_confirmation,
            );

            if let Ok(link) = link {
                let link = Arc::new(link);
                let packet_task = packet::spawn_packet_cmd_worker(
                    cmd_rx,
                    link.clone(),
                    packets_config.clear_on_start,
                    packets_config.clear_interval,
                    path.clone(),
                );
                task_handles.push(packet_task);

                let link_task = packet::spawn_packet_worker(path.clone(), link);
                task_handles.push(link_task);
            }
        }
    }

    WorkerHandle::new(id, object, cmd_tx, task_handles)
}
