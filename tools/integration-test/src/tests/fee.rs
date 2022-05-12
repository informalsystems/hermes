use ibc::core::ics04_channel::Version;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::fee::{
    ibc_token_transfer_with_fee, register_counterparty_address,
};

#[test]
fn test_channel_with_fee() -> Result<(), Error> {
    run_binary_channel_test(&ChannelWithFeeTest)
}

pub struct ChannelWithFeeTest;

impl TestOverrides for ChannelWithFeeTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl BinaryChannelTest for ChannelWithFeeTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let chain_id_a = chain_driver_a.chain_id();
        let chain_id_b = chain_driver_b.chain_id();

        let denom_a = chains.node_a.denom();
        let tx_config_a = chain_driver_a.tx_config();
        let tx_config_b = chain_driver_b.tx_config();

        let port_a = channel.port_a.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let channel_id_b = channel.channel_id_b.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();
        let relayer_b = wallets_b.relayer();

        info!(
            "registering counterparty address of relayer {} on chain {} to be {} on chain {}",
            relayer_b.address(),
            chain_id_b,
            relayer_a.address(),
            chain_id_a
        );

        chain_driver_b
            .value()
            .runtime
            .block_on(register_counterparty_address(
                &tx_config_b,
                &relayer_b,
                &relayer_a.address(),
                &channel_id_b,
            ))?;

        relayer.with_supervisor(move || {
            let user_a = wallets_a.user1();
            let user_b = wallets_b.user1();

            let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

            let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

            let send_amount = 1000;
            let receive_fee = 300;
            let ack_fee = 200;
            let timeout_fee = 100;

            let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;

            let balance_a2 = balance_a1 - total_sent;

            chain_driver_a
                .value()
                .runtime
                .block_on(ibc_token_transfer_with_fee(
                    &tx_config_a,
                    &port_a,
                    &channel_id_a,
                    &user_a,
                    &user_b.address(),
                    &denom_a,
                    send_amount,
                    receive_fee,
                    ack_fee,
                    timeout_fee,
                ))?;

            let denom_b = derive_ibc_denom(
                &channel.port_b.as_ref(),
                &channel.channel_id_b.as_ref(),
                &denom_a,
            )?;

            info!("Expect user A's balance after transfer: {}", balance_a2);

            chain_driver_a.assert_eventual_wallet_amount(
                &user_a.address(),
                balance_a2,
                &denom_a,
            )?;

            chain_driver_b.assert_eventual_wallet_amount(
                &user_b.address(),
                send_amount,
                &denom_b.as_ref(),
            )?;

            info!(
                "Expect user to be refunded receive timeout fee {} and go from {} to {}",
                timeout_fee,
                balance_a2,
                balance_a2 + timeout_fee + ack_fee
            );

            // receive fee and timeout fee should be refunded,
            // as there is no counterparty address registered.
            chain_driver_a.assert_eventual_wallet_amount(
                &user_a.address(),
                balance_a2 + timeout_fee,
                &denom_a,
            )?;

            info!(
                "Expect relayer to receive ack fee {} and receive fee {} and go from {} to {}",
                ack_fee,
                receive_fee,
                relayer_balance_a,
                relayer_balance_a + ack_fee + receive_fee,
            );

            chain_driver_a.assert_eventual_wallet_amount(
                &relayer_a.address(),
                relayer_balance_a + ack_fee + receive_fee,
                &denom_a,
            )?;

            Ok(())
        })
    }
}
