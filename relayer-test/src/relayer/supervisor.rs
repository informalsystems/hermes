use core::time::Duration;
use crossbeam_channel::{bounded, Sender};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::supervisor::cmd::SupervisorCmd;
use ibc_relayer::supervisor::Supervisor;
use std::cell::Cell;
use tracing::info;

// A wrapper around the SupervisorCmd sender so that we can
// send stop signal to the supervisor before stopping the
// chain drivers to prevent the supervisor from raising
// errors caused by closed connections.
pub struct SupervisorHandle {
    sender: Sender<SupervisorCmd>,
    stopped: Cell<bool>,
}

pub fn spawn_supervisor(
    config: SharedConfig,
    registry: SharedRegistry<impl ChainHandle + 'static>,
) -> SupervisorHandle {
    let (mut supervisor, sender) = Supervisor::new_with_registry(config, registry, None);

    std::thread::spawn(move || {
        supervisor.run_without_health_check().unwrap();
    });

    SupervisorHandle::new(sender)
}

impl SupervisorHandle {
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

impl Drop for SupervisorHandle {
    fn drop(&mut self) {
        self.stop();
    }
}
