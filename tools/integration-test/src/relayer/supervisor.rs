/*!
   Extension to the [`Supervisor`] data type.
*/

use core::time::Duration;
use crossbeam_channel::{bounded, Sender};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::supervisor::cmd::SupervisorCmd;
use ibc_relayer::supervisor::Supervisor;
use std::cell::Cell;
use tracing::info;

/**
    A wrapper around the SupervisorCmd sender so that we can
    send stop signal to the supervisor before stopping the
    chain drivers to prevent the supervisor from raising
    errors caused by closed connections.
*/
pub struct SupervisorHandle {
    sender: Sender<SupervisorCmd>,
    stopped: Cell<bool>,
}

/**
   Spawn a supervisor for testing purpose using the provided
   [`SharedConfig`] and [`SharedRegistry`]. Returns a
   [`SupervisorHandle`] that stops the supervisor when the
   value is dropped.
*/
pub fn spawn_supervisor(
    config: SharedConfig,
    registry: SharedRegistry<impl ChainHandle + 'static>,
) -> SupervisorHandle {
    let (mut supervisor, sender) = Supervisor::new_with_registry(config, registry, None);

    std::thread::spawn(move || {
        // We run the supervisor without health check, as `gaiad` running
        // from Cosmos.nix do not contain version information and would fail
        // the health check.
        // https://github.com/informalsystems/cosmos.nix/issues/53
        supervisor.run_without_health_check().unwrap();
    });

    SupervisorHandle::new(sender)
}

impl SupervisorHandle {
    /**
       Create a new [`SupervisorHandle`] based on the underlying [`SupervisorCmd`]
       sender.
    */
    pub fn new(sender: Sender<SupervisorCmd>) -> Self {
        Self {
            sender,
            stopped: Cell::new(false),
        }
    }

    /**
       Explicitly stop the running supervisor. This is useful in tests where
       the supervisor has to be stopped and restarted explicitly.

       Note that after stopping the supervisor, the only way to restart it
       is by respawning a new supervisor using [`spawn_supervisor`].
    */
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
