use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::{config::Config, supervisor::Supervisor};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(help = "discover and relay on all paths")]
    all: bool,
}

impl StartMultiCmd {
    fn cmd(&self) -> Result<Output, BoxError> {
        let config = &*app_config();
        start(config.clone())
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

fn start(config: Config) -> Result<Output, BoxError> {
    let supervisor = Supervisor::spawn(config).expect("failed to spawn supervisor");
    supervisor.run()?;

    Ok(Output::success_msg("done"))
}
