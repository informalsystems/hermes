use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::config::Config;
use ibc_relayer::supervisor::Supervisor;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = app_config();

        let supervisor = spawn_supervisor(config.clone());
        match supervisor.run() {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(feature = "telemetry")]
fn spawn_supervisor(config: Config) -> Supervisor {
    let state = ibc_telemetry::new_state();

    if config.telemetry.enabled {
        let address = (config.telemetry.host.clone(), config.telemetry.port);
        ibc_telemetry::spawn(address, state.clone());
    }

    Supervisor::spawn(config, state)
}

#[cfg(not(feature = "telemetry"))]
fn spawn_supervisor(config: Config) -> Supervisor {
    if config.telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }

    let telemetry = ibc_relayer::telemetry::TelemetryDisabled;
    Supervisor::spawn(config, telemetry)
}
