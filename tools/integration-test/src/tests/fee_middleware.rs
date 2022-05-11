use ibc::core::ics04_channel::Version;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::fee::ibc_token_transfer_with_fee;

#[test]
fn test_channel_with_fee() -> Result<(), Error> {
    run_binary_channel_test(&ChannelWithFeeTest)
}

pub struct ChannelWithFeeTest;

impl TestOverrides for ChannelWithFeeTest {
    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl BinaryChannelTest for ChannelWithFeeTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let denom_a = chains.node_a.denom();
        let tx_config_a = chain_driver_a.tx_config();

        let port_a = &channel.port_a.as_ref();
        let channel_id_a = &channel.channel_id_a.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let user_a1 = wallets_a.user1();
        let user_b1 = wallets_b.user1();

        let relayer_a = wallets_a.relayer();

        let balance_a1 = chain_driver_a.query_balance(&user_a1.address(), &denom_a)?;

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
                port_a,
                channel_id_a,
                &user_a1,
                &user_b1.address(),
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

        chain_driver_a.assert_eventual_wallet_amount(&user_a1.address(), balance_a2, &denom_a)?;

        chain_driver_b.assert_eventual_wallet_amount(
            &user_b1.address(),
            send_amount,
            &denom_b.as_ref(),
        )?;

        info!(
            "Expect user to be refunded receive fee {} and timeout fee {} and go from {} to {}",
            receive_fee,
            timeout_fee,
            balance_a2,
            balance_a2 + receive_fee + timeout_fee
        );

        // receive fee and timeout fee should be refunded,
        // as there is no counterparty address registered.
        chain_driver_a.assert_eventual_wallet_amount(
            &user_a1.address(),
            balance_a2 + receive_fee + timeout_fee,
            &denom_a,
        )?;

        info!(
            "Expect relayer to receive ack fee {} and go from {} to {}",
            ack_fee,
            relayer_balance_a,
            relayer_balance_a + ack_fee
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &relayer_a.address(),
            relayer_balance_a + ack_fee,
            &denom_a,
        )?;

        Ok(())
    }
}
