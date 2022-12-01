use ibc_relayer::supervisor::SupervisorOptions;
use std::error::Error;
use std::io;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use crossbeam_channel::Sender;

use ibc_relayer::chain::handle::{CachingChainHandle, ChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::rest;
use ibc_relayer::supervisor::{cmd::SupervisorCmd, spawn_supervisor, SupervisorHandle};

use crate::conclude::json;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct StartCmd {
    #[clap(
        long = "full-scan",
        help = "Force a full scan of the chains for clients, connections and channels"
    )]
    full_scan: bool,
}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        let supervisor_handle = make_supervisor::<CachingChainHandle>(config, self.full_scan)
            .unwrap_or_else(|e| {
                Output::error(format!("Hermes failed to start, last error: {}", e)).exit()
            });

        match crate::config::config_path() {
            Some(_) => {
                register_signals(supervisor_handle.sender.clone()).unwrap_or_else(|e| {
                    warn!("failed to install signal handler: {}", e);
                });
            }
            None => {
                warn!("cannot figure out configuration path, skipping registration of signal handlers");
            }
        };

        info!("Hermes has started");

        supervisor_handle.wait();
    }
}

/// Register the SIGHUP and SIGUSR1 signals, and notify the supervisor.
/// - [DEPRECATED] SIGHUP: Trigger a reload of the configuration.
/// - SIGUSR1: Ask the supervisor to dump its state and print it to the console.
fn register_signals(tx_cmd: Sender<SupervisorCmd>) -> Result<(), io::Error> {
    use signal_hook::{consts::signal::*, iterator::Signals};

    let sigs = vec![
        SIGHUP,  // Reload of configuration (disabled)
        SIGUSR1, // Dump state
    ];

    let mut signals = Signals::new(sigs)?;

    std::thread::spawn(move || {
        for signal in &mut signals {
            match signal {
                SIGHUP => warn!(
                    "configuration reloading via SIGHUP has been disabled, \
                     the signal handler will be removed in the future"
                ),
                SIGUSR1 => {
                    info!("dumping state (triggered by SIGUSR1)");

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

#[cfg(feature = "rest-server")]
fn spawn_rest_server(config: &Config) -> Option<rest::Receiver> {
    let _span = tracing::error_span!("rest").entered();

    let rest = config.rest.clone();

    if rest.enabled {
        let rest_config = ibc_relayer_rest::Config::new(rest.host, rest.port);
        let (_, rest_receiver) = ibc_relayer_rest::server::spawn(rest_config);
        Some(rest_receiver)
    } else {
        info!("REST server disabled");
        None
    }
}

#[cfg(not(feature = "rest-server"))]
fn spawn_rest_server(config: &Config) -> Option<rest::Receiver> {
    let rest = config.rest.clone();

    if rest.enabled {
        warn!(
            "REST server enabled in the config but Hermes was built without REST support, \
             build Hermes with --features=rest-server to enable REST support."
        );

        None
    } else {
        None
    }
}

#[cfg(feature = "telemetry")]
fn spawn_telemetry_server(config: &Config) -> Result<(), Box<dyn Error + Send + Sync>> {
    let _span = tracing::error_span!("telemetry").entered();

    let state = ibc_telemetry::global();

    let telemetry = config.telemetry.clone();
    if telemetry.enabled {
        match ibc_telemetry::spawn((telemetry.host, telemetry.port), state.clone()) {
            Ok((addr, _)) => {
                info!(
                    "telemetry service running, exposing metrics at http://{}/metrics",
                    addr
                );
            }
            Err(e) => {
                error!("telemetry service failed to start: {}", e);
                return Err(e);
            }
        }
    }

    Ok(())
}

#[cfg(not(feature = "telemetry"))]
fn spawn_telemetry_server(config: &Config) -> Result<(), Box<dyn Error + Send + Sync>> {
    if config.telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }

    Ok(())
}

fn make_supervisor<Chain: ChainHandle>(
    config: Config,
    force_full_scan: bool,
) -> Result<SupervisorHandle, Box<dyn Error + Send + Sync>> {
    let registry = SharedRegistry::<Chain>::new(config.clone());
    spawn_telemetry_server(&config)?;

    let rest = spawn_rest_server(&config);

    Ok(spawn_supervisor(
        config,
        registry,
        rest,
        SupervisorOptions {
            health_check: true,
            force_full_scan,
        },
    )?)
}

#[cfg(test)]
mod tests {
    use super::StartCmd;

    use abscissa_core::clap::Parser;

    #[test]
    fn test_start_required_only() {
        assert_eq!(
            StartCmd { full_scan: false },
            StartCmd::parse_from(["test"])
        )
    }

    #[test]
    fn test_start_full_scan() {
        assert_eq!(
            StartCmd { full_scan: true },
            StartCmd::parse_from(["test", "--full-scan"])
        )
    }
}
