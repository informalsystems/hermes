use core::time::Duration;
// use ibc::core::ics24_host::identifier::PortId;
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::config::Config;
use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle};
use std::thread::sleep;

// use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::prelude::*;

// The cosmos ChainHandle handles requests in serial, and a refresh client
// request may get blocked by other operations and cause the refresh to fail
// if the expiry time is too short.
const CLIENT_EXPIRY: Duration = Duration::from_secs(20);

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
        config.mode.connections.enabled = true;
        config.mode.channels.enabled = true;
        for mut chain_config in config.chains.iter_mut() {
            chain_config.trusting_period = Some(CLIENT_EXPIRY);
        }
    }

    fn spawn_supervisor(
        &self,
        _config: &SharedConfig,
        _registry: &SharedRegistry<impl ChainHandle + 'static>,
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
        // let port = PortId::unsafe_new("transfer");

        // let _supervisor =
        //     spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        let sleep_time = CLIENT_EXPIRY + Duration::from_secs(10);

        info!(
            "Sleeping for {} seconds to wait for IBC client to expire",
            sleep_time.as_secs()
        );

        sleep(sleep_time);

        info!("Trying to create connection after client is expired");

        let connection = Connection {
            delay_period: ZERO_DURATION,
            a_side: ConnectionSide::new(chains.handle_a, chains.client_b_to_a.id, None),
            b_side: ConnectionSide::new(chains.handle_b, chains.client_a_to_b.id, None),
        };

        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        // Success logs are only in debug
        connection.build_conn_init_and_send()?;

        // bootstrap_channel_with_chains(&chains, &port, &port)?;

        crate::suspend();
        Ok(())
    }
}
