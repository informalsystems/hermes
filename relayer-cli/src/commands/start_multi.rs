use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::supervisor::Supervisor;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        let config = app_config();

        let supervisor = Supervisor::spawn(config.clone()).expect("failed to spawn supervisor");
        match supervisor.run() {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
