use ibc_test_framework::ibc::denom::derive_ibc_denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

#[test]
fn test_clear_packet() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketTest)
}
pub struct ClearPacketTest;

impl TestOverrides for ClearPacketTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Disabling clear_on_start should make the relayer not
        // relay any packet it missed before starting.
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    // Unordered channel: will permit gaps in the sequence of relayed packets
    fn channel_order(&self) -> Order {
        Order::Unordered
    }
}

impl BinaryChannelTest for ClearPacketTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let amount1 = random_u64_range(1000, 5000);

        info!(
            "Performing IBC transfer with amount {}, which should *not* be relayed",
            amount1
        );

        chains.node_a.chain_driver().transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.address(),
            &wallet_b.address(),
            amount1,
            &denom_a,
        )?;

        sleep(Duration::from_secs(1));

        // Spawn the supervisor only after the first IBC trasnfer
        relayer.with_supervisor(|| {
            sleep(Duration::from_secs(1));

            let amount2 = random_u64_range(1000, 5000);

            info!(
                "Performing IBC transfer with amount {}, which should be relayed",
                amount2
            );

            chains.node_a.chain_driver().transfer_token(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.address(),
                &wallet_b.address(),
                amount2,
                &denom_a,
            )?;

            sleep(Duration::from_secs(1));

            let denom_b = derive_ibc_denom(
                &channel.port_b.as_ref(),
                &channel.channel_id_b.as_ref(),
                &denom_a,
            )?;

            // Wallet on chain A should have both amount deducted.
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                balance_a - amount1 - amount2,
                &denom_a,
            )?;

            // Wallet on chain B should only receive the second IBC transfer
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                amount2,
                &denom_b.as_ref(),
            )?;

            Ok(())
        })
    }
}
