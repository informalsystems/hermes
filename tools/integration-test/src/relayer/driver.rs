use ibc_relayer::chain::handle::ProdChainHandle;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use std::path::PathBuf;

use crate::relayer::supervisor::{spawn_supervisor, SupervisorHandle};
use crate::types::env::{EnvWriter, ExportEnv};

#[derive(Clone)]
pub struct RelayerDriver {
    /**
       The path to the relayer config saved on the filesystem.

       This allows users to test the relayer manually with the config file
       while the test is suspended.
    */
    pub config_path: PathBuf,

    /**
       The relayer [`Config`](ibc_relayer::config::Config) that is shared
       with the [`Registry`](ibc_relayer::registry::Registry).

       Use this shared config when spawning new supervisor using
       [`spawn_supervisor`](crate::relayer::supervisor::spawn_supervisor).
    */
    pub config: SharedConfig,

    /**
       The relayer chain [`Registry`](ibc_relayer::registry::Registry)
       that is shared with any running
       [`Supervisor`](ibc_relayer::supervisor::Supervisor).

       Use this shared registry when spawning new supervisor using
       [`spawn_supervisor`](crate::relayer::supervisor::spawn_supervisor).
    */
    pub registry: SharedRegistry<ProdChainHandle>,
}

impl RelayerDriver {
    pub fn spawn_supervisor(&self) -> SupervisorHandle {
        spawn_supervisor(self.config.clone(), self.registry.clone())
    }
}

impl ExportEnv for RelayerDriver {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("RELAYER_CONFIG", &format!("{}", self.config_path.display()));
    }
}
