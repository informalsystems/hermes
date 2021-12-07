use core::time::Duration;
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle};
use ibc_relayer::worker::client::spawn_refresh_client;
use std::thread::sleep;

use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::prelude::*;

// The cosmos ChainHandle handles requests in serial, and a refresh client
// request may get blocked by other operations and cause the refresh to fail
// if the expiry time is too short.
const CLIENT_EXPIRY: Duration = Duration::from_secs(15);

#[test]
fn test_client_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ClientExpirationTest)
}

pub struct ClientExpirationTest;

impl TestOverrides for ClientExpirationTest {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: config::Clients {
                enabled: true,
                refresh: true,
                misbehaviour: true,
            },
            connections: config::Connections { enabled: true },
            channels: config::Channels { enabled: true },
            packets: config::Packets {
                enabled: true,
                clear_interval: config::default::clear_packets_interval(),
                clear_on_start: true,
                filter: false,
                tx_confirmation: true,
            },
        };

        for mut chain_config in config.chains.iter_mut() {
            chain_config.trusting_period = Some(CLIENT_EXPIRY);
        }
    }

    fn spawn_supervisor(
        &self,
        _config: &SharedConfig,
        _registry: &SharedRegistry<impl ChainHandle>,
    ) -> Result<Option<SupervisorHandle>, Error> {
        Ok(None)
    }
}

impl BinaryChainTest for ClientExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        // let _refresh_task_a = spawn_refresh_client(
        //     chains.client_b_to_a.clone(),
        // );

        // let _refresh_task_b = spawn_refresh_client(
        //     chains.client_a_to_b.clone(),
        // );

        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        let sleep_time = CLIENT_EXPIRY + Duration::from_secs(5);

        info!(
            "Sleeping for {} seconds to wait for IBC client to expire",
            sleep_time.as_secs()
        );

        sleep(sleep_time);

        info!("Trying to create connection after client is expired");

        // let _supervisor =
        //     spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        let connection = Connection {
            delay_period: ZERO_DURATION,
            a_side: ConnectionSide::new(
                chains.handle_a.clone(),
                chains.client_b_to_a.id.clone(),
                None,
            ),
            b_side: ConnectionSide::new(
                chains.handle_b.clone(),
                chains.client_a_to_b.id.clone(),
                None,
            ),
        };

        // Success logs are only in debug
        connection.build_conn_init_and_send()?;

        // let port = PortId::unsafe_new("transfer");
        // bootstrap_channel_with_chains(&chains, &port, &port)?;

        crate::suspend();
        Ok(())
    }
}
