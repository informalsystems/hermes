use core::time::Duration;
use crossbeam_channel::Sender;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::supervisor::cmd::SupervisorCmd;
use std::thread;

use super::client_server::ChainClientServer;

pub struct ChainDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    // Have this as first field to drop the supervisor
    // first before stopping the chain driver.
    pub supervisor_cmd_sender: SupervisorCmdSender,

    pub config: Config,

    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    pub client_b_to_a: ForeignClient<ChainA, ChainB>,

    pub side_a: ChainClientServer<ChainA>,
    pub side_b: ChainClientServer<ChainB>,
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
pub struct SupervisorCmdSender(pub Sender<SupervisorCmd>);

impl Drop for SupervisorCmdSender {
    fn drop(&mut self) {
        let _ = self.0.send(SupervisorCmd::Stop);
        thread::sleep(Duration::from_millis(1000));
    }
}
