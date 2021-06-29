use std::error::Error;

use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::config::Config;
use ibc_relayer::supervisor::Supervisor;

use crate::conclude::Output;
use crate::config;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = app_config();

        // No chain is preconfigured
        if config.chains.is_empty() {
            Output::error(config::zero_chain_error()).exit();
        };

        match spawn_supervisor(config.clone()).and_then(|s| {
            info!("Hermes has started");
            s.run()
        }) {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(format!("Hermes failed to start, last error: {}", e)).exit(),
        }
    }
}

#[cfg(feature = "telemetry")]
fn spawn_supervisor(config: Config) -> Result<Supervisor, Box<dyn Error + Send + Sync>> {
    let state = ibc_telemetry::new_state();

    if config.telemetry.enabled {
        let address = (config.telemetry.host.clone(), config.telemetry.port);

        match ibc_telemetry::spawn(address, state.clone()) {
            Ok((addr, _)) => {
                info!(
                    "telemetry service running, exposing metrics at {}/metrics",
                    addr
                );
            }
            Err(e) => {
                error!("telemetry service failed to start: {}", e);
                return Err(e);
            }
        }
    }

    Ok(Supervisor::spawn(config, state))
}

#[cfg(not(feature = "telemetry"))]
fn spawn_supervisor(config: Config) -> Result<Supervisor, Box<dyn Error + Send + Sync>> {
    if config.telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }

    let telemetry = ibc_relayer::telemetry::TelemetryDisabled;
    Ok(Supervisor::spawn(config, telemetry))
}
