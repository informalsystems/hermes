use core::time::Duration;
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle};
use ibc_relayer::worker::client::spawn_refresh_client;
use std::thread::sleep;

use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::bootstrap::binary::connection::bootstrap_connection;
use crate::prelude::*;
use crate::relayer::channel::init_channel;
use crate::relayer::connection::init_connection;

// The cosmos ChainHandle handles requests in serial, and a refresh client
// request may get blocked by other operations and cause the refresh to fail
// if the expiry time is too short.
const CLIENT_EXPIRY: Duration = Duration::from_secs(15);

/**
   A manual test to verify that the connection worker is properly terminated
   instead of looping indefinitely when it is not possible to perform
   connection handshake due to the client being expired or frozen.

   Since the test involves long-running background tasks, it has to
   be verified manually by inspecting the logs. Run the test with
   the following command:

   ```bash
   RUST_BACKTRACE=0 RUST_LOG=info cargo test -p ibc-integration-test -- --nocapture --test-threads=1 test_connection_expiration
   ```

   And you should see simple failure toward the end of the test that looks like:

   ```log
   INFO ibc_integration_test::tests::client_expiration: Sleeping for 20 seconds to wait for IBC client to expire
   INFO ibc_integration_test::tests::client_expiration: Trying to create connection after client is expired
   INFO ibc_relayer::chain::cosmos: [ibc-beta-25716970] waiting for commit of tx hashes(s) 15030785428E01BE2EAEE35275A29977593F3E5ADCC5ED8AA7CDA4D1EDEC6515
   WARN ibc_integration_test::util::suspend: suspending the test indefinitely. you can still interact with any spawned chains and relayers
   ERROR ibc_relayer::connection: failed to establish connection handshake on frozen client:
   0: failed during an operation on client (07-tendermint-0) hosted by chain (ibc-beta-25716970)
   1: client 07-tendermint-0 on chain id ibc-beta-25716970 is expired or frozen
   ERROR ibc_relayer::util::task: aborting task connection_worker after encountering fatal error:
   0: Packet worker failed after 1 retries
   ```

   The error above should not repeat more than once. In the original code,
   the connection worker would keep retrying and indefinitely flooding
   the log with errors.
*/
#[test]
fn test_connection_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionExpirationTest)
}

#[test]
fn test_channel_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ChannelExpirationTest)
}

#[test]
fn test_client_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ClientExpirationTest)
}

fn wait_for_client_expiry() {
    let sleep_time = CLIENT_EXPIRY + Duration::from_secs(5);

    info!(
        "Sleeping for {} seconds to wait for IBC client to expire",
        sleep_time.as_secs()
    );

    sleep(sleep_time);
}

pub struct ExpirationTestOverrides;

pub struct ConnectionExpirationTest;

pub struct ChannelExpirationTest;

pub struct ClientExpirationTest;

impl TestOverrides for ExpirationTestOverrides {
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

impl HasOverrides for ClientExpirationTest {
    type Overrides = ExpirationTestOverrides;

    fn get_overrides(&self) -> &ExpirationTestOverrides {
        &ExpirationTestOverrides
    }
}

impl HasOverrides for ConnectionExpirationTest {
    type Overrides = ExpirationTestOverrides;

    fn get_overrides(&self) -> &ExpirationTestOverrides {
        &ExpirationTestOverrides
    }
}

impl HasOverrides for ChannelExpirationTest {
    type Overrides = ExpirationTestOverrides;

    fn get_overrides(&self) -> &ExpirationTestOverrides {
        &ExpirationTestOverrides
    }
}

impl BinaryChainTest for ConnectionExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        wait_for_client_expiry();

        info!("Trying to create connection after client is expired");

        init_connection(&chains)?;

        crate::suspend();
    }
}

impl BinaryChainTest for ChannelExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let refresh_task_a = spawn_refresh_client(chains.client_b_to_a.clone());

        let refresh_task_b = spawn_refresh_client(chains.client_a_to_b.clone());

        let connection = bootstrap_connection(&chains.client_b_to_a, &chains.client_a_to_b, false)?;

        refresh_task_a.shutdown_and_wait();
        refresh_task_b.shutdown_and_wait();

        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        wait_for_client_expiry();

        info!("Trying to create channel after client is expired");

        let port = PortId::unsafe_new("transfer");
        init_channel(&chains, &connection, port.clone(), port)?;

        crate::suspend();
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

        // Success logs are only in debug
        init_connection(&chains)?;

        // let port = PortId::unsafe_new("transfer");
        // bootstrap_channel_with_chains(&chains, &port, &port)?;

        crate::suspend();
        Ok(())
    }
}
