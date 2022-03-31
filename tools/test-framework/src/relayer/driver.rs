/*!
   Driver for spawning the relayer.
*/

use ibc_relayer::chain::handle::CountingAndCachingChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle, SupervisorOptions};
use std::path::PathBuf;

use crate::error::Error;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::util::suspend::hang_on_error;

/**
   Encapsulates the parameters needed to spawn the relayer supervisor.

   In the future, other methods that correspond to the relayer CLI can
   also be added here.
*/
#[derive(Clone)]
pub struct RelayerDriver {
    /**
       The path to the relayer config saved on the filesystem.

       This allows users to test the relayer manually with the config file
       while the test is suspended.
    */
    pub config_path: PathBuf,

    /**
       The relayer [`Config`]. Use this config when spawning new supervisor
       using [`spawn_supervisor`](ibc_relayer::supervisor::spawn_supervisor).
    */
    pub config: Config,

    /**
       The relayer chain [`Registry`](ibc_relayer::registry::Registry)
       that is shared with any running supervisor.

       Use this shared registry when spawning new supervisor using
       [`spawn_supervisor`](ibc_relayer::supervisor::spawn_supervisor).
    */
    pub registry: SharedRegistry<CountingAndCachingChainHandle>,

    /**
       Whether the driver should hang the test when the continuation
       closure in [`with_supervisor`](Self::with_supervisor) fails.
    */
    pub hang_on_fail: bool,
}

impl RelayerDriver {
    /**
       Spawns the relayer supervisor and return the [`SupervisorHandle`].
    */
    pub fn spawn_supervisor(&self) -> Result<SupervisorHandle, Error> {
        spawn_supervisor(
            self.config.clone(),
            self.registry.clone(),
            None,
            SupervisorOptions {
                health_check: false,
                force_full_scan: false,
            },
        )
        .map_err(Error::supervisor)
    }

    /**
       Spawns the relayer supervisor and then executes the provided continuation
       with the supervisor running.

       The supervisor is stopped after the continuation returned. If
       `hang_on_fail` is set to true, the call will suspend if the continuation
       returns error.
    */
    pub fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
        let _handle = self.spawn_supervisor()?;

        hang_on_error(self.hang_on_fail, cont)
    }
}

impl ExportEnv for RelayerDriver {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("RELAYER_CONFIG", &format!("{}", self.config_path.display()));
    }
}
