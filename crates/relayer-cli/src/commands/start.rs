use std::{
    error::Error,
    io,
};

use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};
use crossbeam_channel::Sender;
use ibc_relayer::{
    chain::handle::{
        CachingChainHandle,
        ChainHandle,
    },
    config::Config,
    registry::SharedRegistry,
    rest,
    supervisor::{
        cmd::SupervisorCmd,
        spawn_supervisor,
        SupervisorHandle,
        SupervisorOptions,
    },
    util::debug_section::DebugSection,
};

use crate::{
    conclude::{
        json,
        Output,
    },
    prelude::*,
};

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
        let app = app_reader();

        if app.debug_enabled(DebugSection::ProfilingJson) {
            use std::{
                env,
                path::Path,
            };

            use ibc_relayer::util::profiling::open_or_create_profile_file;

            let profile_dir = env::var("PROFILING_DIR").unwrap_or_else(|_| ".".to_string());

            let now = time::OffsetDateTime::now_utc();
            let path_str = format!(
                "{}/hermes-{:04}-{:02}-{:02}-{:02}{:02}{:02}-prof.json",
                profile_dir,
                now.year(),
                now.month(),
                now.day(),
                now.hour(),
                now.minute(),
                now.second()
            );

            open_or_create_profile_file(Path::new(&path_str));
        }

        let config = (*app_config()).clone();

        let options = SupervisorOptions {
            force_full_scan: self.full_scan,
            health_check: true,
        };

        let supervisor_handle = make_supervisor::<CachingChainHandle>(config, options)
            .unwrap_or_else(|e| {
                Output::error(format!("Hermes failed to start, last error: {e}")).exit()
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
    use signal_hook::{
        consts::signal::*,
        iterator::Signals,
    };

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
                                    Ok(out) => println!("{out}"),
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
    use ibc_relayer::util::spawn_blocking;

    let _span = tracing::error_span!("rest").entered();

    let rest = config.rest.clone();

    if !rest.enabled {
        info!("REST server disabled");
        return None;
    }

    let (tx, rx) = crossbeam_channel::unbounded();

    spawn_blocking(async move {
        let result = ibc_relayer_rest::spawn((rest.host.as_str(), rest.port), tx);

        match result {
            Ok(handle) => {
                info!(
                    "REST service running, exposing REST API at http://{}:{}",
                    rest.host, rest.port
                );

                if let Err(e) = handle.await {
                    error!("REST service crashed with error: {e}");
                }
            }
            Err(e) => {
                error!("REST service failed to start: {e}");
            }
        }
    });

    Some(rx)
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
fn spawn_telemetry_server(config: &Config) {
    use ibc_relayer::util::spawn_blocking;

    let _span = tracing::error_span!("telemetry").entered();

    let state = ibc_telemetry::init(
        config.telemetry.buckets.latency_submitted.range.clone(),
        config.telemetry.buckets.latency_submitted.buckets,
        config.telemetry.buckets.latency_confirmed.range.clone(),
        config.telemetry.buckets.latency_confirmed.buckets,
    );
    let telemetry = config.telemetry.clone();

    if !telemetry.enabled {
        info!("telemetry disabled");
        return;
    }

    spawn_blocking(async move {
        let result = ibc_telemetry::spawn((telemetry.host, telemetry.port), state.clone());

        match result {
            Ok((addr, handle)) => {
                info!("telemetry service running, exposing metrics at http://{addr}/metrics");

                if let Err(e) = handle.await {
                    error!("telemetry service crashed with error: {e}");
                }
            }
            Err(e) => error!("telemetry service failed to start: {e}"),
        }
    });
}

#[cfg(not(feature = "telemetry"))]
fn spawn_telemetry_server(config: &Config) {
    if config.telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }
}

fn make_supervisor<Chain: ChainHandle>(
    config: Config,
    options: SupervisorOptions,
) -> Result<SupervisorHandle, Box<dyn Error + Send + Sync>> {
    let registry = SharedRegistry::<Chain>::new(config.clone());

    spawn_telemetry_server(&config);

    let rest_rx = spawn_rest_server(&config);

    Ok(spawn_supervisor(config, registry, rest_rx, options)?)
}

#[cfg(test)]
mod tests {
    use abscissa_core::clap::Parser;

    use super::StartCmd;

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
