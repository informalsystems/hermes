use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::supervisor::Supervisor;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(help = "discover and relay on all paths for all chains in the config file")]
    all: bool,
}

impl StartMultiCmd {
    fn cmd(&self) -> Result<Output, BoxError> {
        let config = app_config();

        let supervisor = Supervisor::spawn(config.clone()).expect("failed to spawn supervisor");
        supervisor.run()?;

        Ok(Output::success_msg("done"))
    }
}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        match self.cmd() {
            Ok(output) => output.exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
