use core::time::Duration;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle};
use ibc_relayer::worker::client::spawn_refresh_client;
use std::thread::sleep;

use crate::bootstrap::binary::chain::bootstrap_foreign_client;
use crate::bootstrap::binary::channel::{
    bootstrap_channel_with_chains, bootstrap_channel_with_connection,
};
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
   RUST_BACKTRACE=0 RUST_LOG=info cargo test --features manual \
     -p ibc-integration-test -- test_connection_expiration
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
   0: Worker failed after 1 retries
   ```

   The error above should not repeat more than once. In the original code,
   the connection worker would keep retrying and indefinitely flooding
   the log with errors.
*/
#[test]
fn test_connection_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionExpirationTest)
}

/**
   A manual test to verify that the channel worker is properly terminated
   instead of looping indefinitely when it is not possible to perform
   channel handshake due to the client being expired or frozen.

   Since the test involves long-running background tasks, it has to
   be verified manually by inspecting the logs. Run the test with
   the following command:

   ```bash
   RUST_BACKTRACE=0 RUST_LOG=info cargo test --features manual \
     -p ibc-integration-test -- test_channel_expiration
   ```

   And you should see simple failure toward the end of the test that looks like:

   ```log
    INFO ibc_integration_test::tests::manual::client_expiration: Trying to create channel after client is expired
    INFO ibc_relayer::chain::cosmos: [ibc-beta-f6611435] waiting for commit of tx hashes(s) 1360595FB238142B7EEF672D2267A6874F6EF0E1C2FAC8CCC72B44EDC6AF8A49
    WARN ibc_integration_test::util::suspend: suspending the test indefinitely. you can still interact with any spawned chains and relayers
    ERROR ibc_relayer::channel: failed to establish channel handshake on frozen client:
    0: failed during an operation on client (07-tendermint-0) hosted by chain (ibc-alpha-995f3fa8)
    1: client 07-tendermint-0 on chain id ibc-alpha-995f3fa8 is expired or frozen
    ERROR ibc_relayer::util::task: aborting task channel_worker after encountering fatal error:
    0: Worker failed after 1 retries
   ```

   The error above should not repeat more than once. In the original code,
   the connection worker would keep retrying and indefinitely flooding
   the log with errors.
*/
#[test]
fn test_channel_expiration() -> Result<(), Error> {
    run_binary_chain_test(&ChannelExpirationTest)
}

#[test]
fn test_packet_expiration() -> Result<(), Error> {
    run_binary_chain_test(&PacketExpirationTest)
}

#[test]
fn test_create_on_expired_client() -> Result<(), Error> {
    run_binary_chain_test(&CreateOnExpiredClientTest)
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

pub struct PacketExpirationTest;

pub struct CreateOnExpiredClientTest;

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
                clear_interval: 10,
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

impl BinaryChainTest for ConnectionExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        // We spawn a supervisor first, but the refresh client is not
        // triggered because it is currently tied to channels.
        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        wait_for_client_expiry();

        info!("Trying to create connection after client is expired");

        // We can submit an CONN_INIT packet and the connection worker will
        // pick it up, and we want to observe that it abort due to frozen client
        // rather than looping indefinitely.

        init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_b_to_a.tagged_client_id(),
            &chains.client_a_to_b.tagged_client_id(),
        )?;

        sleep(Duration::from_secs(10));

        info!("Trying to new connection and worker after previous connection worker failed");

        let client_b_to_a_2 = bootstrap_foreign_client(&chains.handle_b, &chains.handle_a)?;

        let client_a_to_b_2 = bootstrap_foreign_client(&chains.handle_a, &chains.handle_b)?;

        // The second init connection on an unexpired client should succeed.

        let _refresh_task_a = spawn_refresh_client(client_b_to_a_2.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let _refresh_task_b = spawn_refresh_client(client_a_to_b_2.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &client_b_to_a_2.tagged_client_id(),
            &client_a_to_b_2.tagged_client_id(),
        )?;

        crate::suspend();
    }
}

impl BinaryChainTest for ChannelExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let refresh_task_a = spawn_refresh_client(chains.client_b_to_a.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let refresh_task_b = spawn_refresh_client(chains.client_a_to_b.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let connection = bootstrap_connection(&chains.client_b_to_a, &chains.client_a_to_b, false)?;

        refresh_task_a.shutdown_and_wait();
        refresh_task_b.shutdown_and_wait();

        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        wait_for_client_expiry();

        info!("Trying to create channel after client is expired");

        init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection.connection_id_a.as_ref(),
            &connection.connection_id_b.as_ref(),
            &tagged_transfer_port().as_ref(),
            &tagged_transfer_port().as_ref(),
        )?;

        crate::suspend();
    }
}

impl BinaryChainTest for PacketExpirationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let refresh_task_a = spawn_refresh_client(chains.client_b_to_a.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let refresh_task_b = spawn_refresh_client(chains.client_a_to_b.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let channels = bootstrap_channel_with_chains(
            &chains,
            &PortId::transfer(),
            &PortId::transfer(),
            false,
        )?;

        refresh_task_a.shutdown_and_wait();
        refresh_task_b.shutdown_and_wait();

        wait_for_client_expiry();

        let _supervisor =
            spawn_supervisor(chains.config.clone(), chains.registry.clone(), None, false)?;

        chains.node_a.chain_driver().transfer_token(
            &channels.port_a.as_ref(),
            &channels.channel_id_a.as_ref(),
            &chains.node_a.wallets().user1().address(),
            &chains.node_b.wallets().user1().address(),
            100,
            &chains.node_a.denom(),
        )?;

        // The second IBC transfer should be ignored, as the packet worker
        // is terminated

        sleep(Duration::from_secs(15));

        info!("sending a second IBC transfer");

        chains.node_a.chain_driver().transfer_token(
            &channels.port_a.as_ref(),
            &channels.channel_id_a.as_ref(),
            &chains.node_a.wallets().user1().address(),
            &chains.node_b.wallets().user1().address(),
            100,
            &chains.node_a.denom(),
        )?;

        suspend();
    }
}

impl BinaryChainTest for CreateOnExpiredClientTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let refresh_task_a = spawn_refresh_client(chains.client_b_to_a.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        let refresh_task_b = spawn_refresh_client(chains.client_a_to_b.clone())
            .ok_or_else(|| eyre!("expect refresh task spawned"))?;

        // Create a connection before the IBC client expires, so that we can try create
        // new channel with the connection after the client expired.
        let connection = bootstrap_connection(&chains.client_b_to_a, &chains.client_a_to_b, false)?;

        refresh_task_a.shutdown_and_wait();
        refresh_task_b.shutdown_and_wait();

        wait_for_client_expiry();

        info!("trying to bootstrap connection after IBC client is expired");

        let res = bootstrap_connection(&chains.client_b_to_a, &chains.client_a_to_b, false);
        match res {
            Ok(_) => return Err(eyre!("expected bootstrap_connection to fail")),
            Err(e) => {
                info!("bootstrap_connection failed with expected error {}", e);
            }
        }

        sleep(Duration::from_secs(5));

        info!("trying to bootstrap channel after IBC client is expired");

        let res = bootstrap_channel_with_connection(
            &chains.handle_a,
            &chains.handle_b,
            connection,
            &DualTagged::new(&PortId::transfer()),
            &DualTagged::new(&PortId::transfer()),
            false,
        );

        match res {
            Ok(_) => return Err(eyre!("expected bootstrap_channel_with_connection to fail")),
            Err(e) => {
                info!(
                    "bootstrap_channel_with_connection failed with expected error {}",
                    e
                );
            }
        }

        Ok(())
    }
}

impl HasOverrides for CreateOnExpiredClientTest {
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

impl HasOverrides for PacketExpirationTest {
    type Overrides = ExpirationTestOverrides;

    fn get_overrides(&self) -> &ExpirationTestOverrides {
        &ExpirationTestOverrides
    }
}
