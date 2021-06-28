use std::error::Error;
use std::io;
use std::sync::{Arc, RwLock};

use abscissa_core::{Command, Options, Runnable};
use crossbeam_channel::Sender;

use ibc_relayer::config::reload::ConfigReload;
use ibc_relayer::config::Config;
use ibc_relayer::supervisor::{cmd::SupervisorCmd, Supervisor};

use crate::conclude::json;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = (*app_config()).clone();
        let config = Arc::new(RwLock::new(config));

        let (supervisor, tx_cmd) = make_supervisor(config.clone()).unwrap_or_else(|e| {
            Output::error(format!("Hermes failed to start, last error: {}", e)).exit();
            unreachable!()
        });

        match crate::config::config_path() {
            Some(config_path) => {
                let reload = ConfigReload::new(config_path, config, tx_cmd.clone());
                register_signals(reload, tx_cmd).unwrap_or_else(|e| {
                    warn!("failed to install signal handler: {}", e);
                });
            }
            None => {
                warn!("cannot figure out configuration path, skipping registration of signal handlers");
            }
        };

        info!("Hermes has started");
        match supervisor.run() {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(format!("Hermes failed to start, last error: {}", e)).exit(),
        }
    }
}

/// Register the SIGHUP and SIGUSR1 signals, and notify the supervisor.
/// - SIGHUP: Trigger a reload of the configuration.
/// - SIGUSR1: Ask the supervisor to dump its state and print it to the console.
fn register_signals(reload: ConfigReload, tx_cmd: Sender<SupervisorCmd>) -> Result<(), io::Error> {
    use signal_hook::{consts::signal::*, iterator::Signals};

    let sigs = vec![
        SIGHUP,  // Reload of configuration
        SIGUSR1, // Dump state
    ];

    let mut signals = Signals::new(&sigs)?;

    std::thread::spawn(move || {
        for signal in &mut signals {
            match signal {
                SIGHUP => {
                    info!("reloading configuration (triggered by SIGHUP)");
                    match reload.reload() {
                        Ok(true) => info!("configuration successfully reloaded"),
                        Ok(false) => info!("configuration did not change"),
                        Err(e) => error!("failed to reload configuration: {}", e),
                    }
                }
                SIGUSR1 => {
                    info!("Dumping state (triggered by SIGUSR1)");

                    let (tx, rx) = crossbeam_channel::bounded(1);
                    tx_cmd.try_send(SupervisorCmd::DumpState(tx)).unwrap();

                    std::thread::spawn(move || {
                        if let Ok(state) = rx.recv() {
                            if json() {
                                match serde_json::to_string(&state) {
                                    Ok(out) => println!("{}", out),
                                    Err(e) => {
                                        error!("failed to serialize relayer state to JSON: {}", e)
                                    }
                                }
                            } else {
                                state.print_info();
                            }
                        }
                    });
                }

                _ => (),
            }
        }
    });

    Ok(())
}

#[cfg(feature = "telemetry")]
fn make_supervisor(
    config: Arc<RwLock<Config>>,
) -> Result<(Supervisor, Sender<SupervisorCmd>), Box<dyn Error + Send + Sync>> {
    let state = ibc_telemetry::new_state();

    let telemetry = config.read().expect("poisoned lock").telemetry.clone();
    if telemetry.enabled {
        match ibc_telemetry::spawn((telemetry.host, telemetry.port), state.clone()) {
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

    Ok(Supervisor::new(config, state))
}

#[cfg(not(feature = "telemetry"))]
fn make_supervisor(
    config: Arc<RwLock<Config>>,
) -> Result<(Supervisor, Sender<SupervisorCmd>), Box<dyn Error + Send + Sync>> {
    if config.read().expect("poisoned lock").telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }

    let telemetry = ibc_relayer::telemetry::TelemetryDisabled;
    Ok(Supervisor::new(config, telemetry))
}
