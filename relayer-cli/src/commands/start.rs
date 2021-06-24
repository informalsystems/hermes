use std::error::Error;
use std::sync::{Arc, RwLock};

use abscissa_core::{Command, Options, Runnable};
use crossbeam_channel::Sender;

use ibc_relayer::config::reload::ConfigReload;
use ibc_relayer::config::Config;
use ibc_relayer::supervisor::{Supervisor, SupervisorCmd};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartCmd {}

impl Runnable for StartCmd {
    fn run(&self) {
        let config = (*app_config()).clone();
        let config = Arc::new(RwLock::new(config));

        let (supervisor, tx_cmd) = spawn_supervisor(config.clone()).unwrap_or_else(|e| {
            Output::error(format!("Hermes failed to start, last error: {}", e)).exit();
            unreachable!()
        });

        match crate::config::config_path() {
            Some(config_path) => {
                let reload = ConfigReload::new(config_path, config, tx_cmd);
                register_signal(reload).unwrap_or_else(|e| {
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

use std::io;
fn register_signal(reload: ConfigReload) -> Result<(), io::Error> {
    use signal_hook::{consts::signal::*, iterator::Signals};

    let sigs = vec![
        SIGHUP, // Reload of configuration
    ];

    let mut signals = Signals::new(&sigs)?;

    std::thread::spawn(move || {
        for signal in &mut signals {
            if signal == SIGHUP {
                info!("Reloading configuration (triggered by SIGHUP)");
                if let Err(e) = reload.reload() {
                    error!("failed to reload configuration: {}", e);
                }
            }
        }
    });

    Ok(())
}

#[cfg(feature = "telemetry")]
fn spawn_supervisor(
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

    let supervisor = Supervisor::spawn(config, state);

    // std::thread::spawn(move || {
    //     use ibc_relayer::config::ChainConfig;
    //     use ibc_relayer::supervisor::SupervisorCmd;
    //     use std::time::Duration;

    //     /// Returns a very minimal chain configuration, to be used in initializing `MockChain`s.
    //     fn get_basic_chain_config() -> ChainConfig {
    //         let config = r#"
    //                 id = 'ibc-2'
    //                 rpc_addr = 'http://127.0.0.1:26457'
    //                 grpc_addr = 'http://127.0.0.1:9092'
    //                 websocket_addr = 'ws://127.0.0.1:26457/websocket'
    //                 rpc_timeout = '10s'
    //                 account_prefix = 'cosmos'
    //                 key_name = 'testkey'
    //                 store_prefix = 'ibc'
    //                 max_gas = 20000000
    //                 gas_price = { price = 0.001, denom = 'stake' }
    //                 clock_drift = '5s'
    //                 trusting_period = '14days'
    //                 trust_threshold = { numerator = '1', denominator = '3' }
    //                 "#;

    //         toml::from_str(config).unwrap()
    //     }

    //     std::thread::sleep(Duration::from_secs(5));

    //     tx.send(SupervisorCmd::UpdateConfig(ConfigUpdate::Add(
    //         get_basic_chain_config(),
    //     )))
    //     .unwrap();

    //     std::thread::sleep(Duration::from_secs(5));

    //     tx.send(SupervisorCmd::UpdateConfig(ConfigUpdate::Remove(
    //         "ibc-0".parse().unwrap(),
    //     )))
    //     .unwrap();
    // });

    Ok(supervisor)
}

#[cfg(not(feature = "telemetry"))]
fn spawn_supervisor(
    config: Config,
) -> Result<(Supervisor, Sender<SupervisorCmd>), Box<dyn Error + Send + Sync>> {
    if config.telemetry.enabled {
        warn!(
            "telemetry enabled in the config but Hermes was built without telemetry support, \
             build Hermes with --features=telemetry to enable telemetry support."
        );
    }

    let telemetry = ibc_relayer::telemetry::TelemetryDisabled;
    Ok(Supervisor::spawn(config, telemetry))
}
