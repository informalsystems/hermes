use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::supervisor::Supervisor;
use ibc_relayer::telemetry;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = app_config();

        let telemetry = telemetry::spawn(
            config.global.telemetry_port,
            config.global.telemetry_enabled,
        );

        let supervisor =
            Supervisor::spawn(config.clone(), telemetry).expect("failed to spawn supervisor");

        match supervisor.run() {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}
