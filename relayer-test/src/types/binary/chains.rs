use core::time::Duration;
use crossbeam_channel::{bounded, Sender};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::supervisor::cmd::SupervisorCmd;
use std::cell::Cell;
use tracing::info;

use crate::types::single::client_server::ChainClientServer;

pub struct ChainDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub supervisor_cmd_sender: SupervisorCmdSender,

    pub side_a: ChainClientServer<ChainA>,

    pub side_b: ChainClientServer<ChainB>,

    pub config: Config,

    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    pub client_b_to_a: ForeignClient<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ChainDeployment<ChainA, ChainB> {
    pub fn flip(self) -> ChainDeployment<ChainB, ChainA> {
        ChainDeployment {
            supervisor_cmd_sender: self.supervisor_cmd_sender,
            config: self.config,
            client_a_to_b: self.client_b_to_a,
            client_b_to_a: self.client_a_to_b,
            side_a: self.side_b,
            side_b: self.side_a,
        }
    }
}

// A wrapper around the SupervisorCmd sender so that we can
// send stop signal to the supervisor before stopping the
// chain drivers to prevent the supervisor from raising
// errors caused by closed connections.
pub struct SupervisorCmdSender {
    sender: Sender<SupervisorCmd>,
    stopped: Cell<bool>,
}

impl SupervisorCmdSender {
    pub fn new(sender: Sender<SupervisorCmd>) -> Self {
        Self {
            sender,
            stopped: Cell::new(false),
        }
    }

    pub fn stop(&self) {
        if !self.stopped.get() {
            info!("stopping supervisor");
            self.stopped.set(true);
            let (sender, receiver) = bounded(1);
            let _ = self.sender.send(SupervisorCmd::Stop(sender));
            let _ = receiver.recv_timeout(Duration::from_secs(5));
        }
    }
}

impl Drop for SupervisorCmdSender {
    fn drop(&mut self) {
        self.stop();
    }
}
