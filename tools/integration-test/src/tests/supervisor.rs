use ibc_relayer::config::{
    self,
    Config,
    ModeConfig,
};
use ibc_test_framework::{
    ibc::denom::derive_ibc_denom,
    prelude::*,
    relayer::{
        channel::{
            assert_eventually_channel_established,
            init_channel,
        },
        connection::{
            assert_eventually_connection_established,
            init_connection,
        },
    },
};

#[test]
fn test_supervisor() -> Result<(), Error> {
    run_binary_chain_test(&SupervisorTest)
}

#[test]
fn test_supervisor_with_scan() -> Result<(), Error> {
    run_binary_channel_test(&SupervisorScanTest {
        clear_on_start: true,
    })
}

#[test]
fn test_supervisor_no_scan() -> Result<(), Error> {
    run_binary_channel_test(&SupervisorScanTest {
        clear_on_start: false,
    })
}

struct SupervisorTest;

impl TestOverrides for SupervisorTest {
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
                tx_confirmation: true,
                ..Default::default()
            },
        };
    }
}

impl BinaryChainTest for SupervisorTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (connection_id_b, _) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.foreign_clients.client_id_a(),
            &chains.foreign_clients.client_id_b(),
        )?;

        let connection_id_a = assert_eventually_connection_established(
            &chains.handle_b,
            &chains.handle_a,
            &connection_id_b.as_ref(),
        )?;

        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (channel_id_b, _) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection_id_a.as_ref(),
            &connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        let channel_id_a = assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channel_id_b.as_ref(),
            &port_b.as_ref(),
        )?;

        let denom_a = chains.node_a.denom();

        let denom_b = derive_ibc_denom(&port_b.as_ref(), &channel_id_b.as_ref(), &denom_a)?;

        // Use the same wallet as the relayer to perform token transfer.
        // This will cause an account sequence mismatch error.
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let transfer_amount = 1000u64;

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        // Perform local transfers for both chains A and B using the relayer's
        // wallet to mess up the account sequence number on both sides.

        chains.node_a.chain_driver().local_transfer_token(
            &chains.node_a.wallets().relayer(),
            &chains.node_a.wallets().user2().address(),
            &denom_a.with_amount(1000u64).as_ref(),
        )?;

        chains.node_b.chain_driver().local_transfer_token(
            &chains.node_b.wallets().relayer(),
            &chains.node_b.wallets().user2().address(),
            &chains.node_b.denom().with_amount(1000u64).as_ref(),
        )?;

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            transfer_amount,
            denom_a
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &port_a.as_ref(),
            &channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(1000u64).as_ref(),
        )?;

        // During the test, you should see error logs showing "account sequence mismatch".
        info!(
            "Packet worker should still succeed and recover from account sequence mismatch error",
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - transfer_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(transfer_amount).as_ref(),
        )?;

        std::thread::sleep(core::time::Duration::from_secs(10));

        Ok(())
    }
}

struct SupervisorScanTest {
    clear_on_start: bool,
}

impl TestOverrides for SupervisorScanTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: config::Clients {
                enabled: false, // disable client workers, otherwise we have to scan
                refresh: true,
                misbehaviour: true,
            },
            connections: config::Connections { enabled: true },
            channels: config::Channels { enabled: true },
            packets: config::Packets {
                enabled: true,
                clear_on_start: self.clear_on_start,
                ..Default::default()
            },
        };
    }

    fn should_spawn_supervisor(&self) -> bool {
        true
    }
}

impl BinaryChannelTest for SupervisorScanTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();
        let fee_denom_a = MonoTagged::new(Denom::base(&config.native_tokens[0]));

        let denom_b = derive_ibc_denom(
            &channels.port_b.as_ref(),
            &channels.channel_id_b.as_ref(),
            &denom_a,
        )?;

        // Use the same wallet as the relayer to perform token transfer.
        // This will cause an account sequence mismatch error.
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let transfer_amount = 1000u64;

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            transfer_amount,
            denom_a
        );

        let dst_height = chains.handle_b().query_latest_height()?;

        chains.node_a.chain_driver().transfer_from_chain(
            &chains.node_a.wallets().user1(),
            &chains.node_b.wallets().user1().address(),
            &channels.port_a.0,
            &channels.channel_id_a.0,
            &denom_a.with_amount(1000u64).as_ref(),
            &fee_denom_a.with_amount(1200u64).as_ref(),
            &dst_height,
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - transfer_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(transfer_amount).as_ref(),
        )?;

        Ok(())
    }
}
