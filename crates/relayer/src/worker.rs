use alloc::sync::Arc;
use core::fmt::{Display, Error as FmtError, Formatter};
use ibc_relayer_types::core::ics04_channel::channel::Order;
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use tracing::error;

use crate::foreign_client::ForeignClient;
use crate::link::{Link, LinkParameters, Resubmit};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    config::Config,
    object::Object,
};

pub mod retry_strategy;

mod error;
pub use error::RunError;

mod handle;
pub use handle::{WorkerData, WorkerHandle};

mod cmd;
pub use cmd::WorkerCmd;

mod map;
pub use map::WorkerMap;

pub mod channel;
pub mod client;
pub mod connection;
pub mod packet;
pub mod wallet;

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

impl Display for WorkerId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
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

    let (cmd_tx, data) = match &object {
        Object::Client(client) => {
            let client = ForeignClient::restore(client.dst_client_id.clone(), chains.b, chains.a);

            let (mut refresh, mut misbehaviour) = (false, false);

            let refresh_task = client::spawn_refresh_client(client.clone());
            if let Some(refresh_task) = refresh_task {
                task_handles.push(refresh_task);
                refresh = true;
            }

            let cmd_tx = if config.mode.clients.misbehaviour {
                let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();
                let misbehavior_task = client::detect_misbehavior_task(cmd_rx, client);
                if let Some(task) = misbehavior_task {
                    task_handles.push(task);
                    misbehaviour = true;
                }

                Some(cmd_tx)
            } else {
                None
            };

            let data = WorkerData::Client {
                misbehaviour,
                refresh,
            };

            (cmd_tx, Some(data))
        }
        Object::Connection(connection) => {
            let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();
            let connection_task =
                connection::spawn_connection_worker(connection.clone(), chains, cmd_rx);
            task_handles.push(connection_task);

            (Some(cmd_tx), None)
        }
        Object::Channel(channel) => {
            let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();
            let channel_task = channel::spawn_channel_worker(channel.clone(), chains, cmd_rx);
            task_handles.push(channel_task);

            (Some(cmd_tx), None)
        }
        Object::Packet(path) => {
            let packets_config = config.mode.packets;
            let link_res = Link::new_from_opts(
                chains.a.clone(),
                chains.b,
                LinkParameters {
                    src_port_id: path.src_port_id.clone(),
                    src_channel_id: path.src_channel_id.clone(),
                },
                packets_config.tx_confirmation,
                packets_config.auto_register_counterparty_payee,
            );

            match link_res {
                Ok(link) => {
                    let channel_ordering = link.a_to_b.channel().ordering;
                    let should_clear_on_start =
                        packets_config.clear_on_start || channel_ordering == Order::Ordered;

                    let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();
                    let link = Arc::new(Mutex::new(link));
                    let resubmit = Resubmit::from_clear_interval(packets_config.clear_interval);

                    let packet_task = packet::spawn_packet_cmd_worker(
                        cmd_rx,
                        link.clone(),
                        should_clear_on_start,
                        packets_config.clear_interval,
                        path.clone(),
                    );
                    task_handles.push(packet_task);

                    let link_task = packet::spawn_packet_worker(path.clone(), link, resubmit);
                    task_handles.push(link_task);

                    (Some(cmd_tx), None)
                }
                Err(e) => {
                    error!("error initializing link object for packet worker: {}", e);
                    (None, None)
                }
            }
        }

        Object::Wallet(wallet) => {
            assert_eq!(wallet.chain_id, chains.a.id());

            let wallet_task = wallet::spawn_wallet_worker(chains.a);
            task_handles.push(wallet_task);

            (None, None)
        }
    };

    WorkerHandle::new(id, object, data, cmd_tx, task_handles)
}
