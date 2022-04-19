use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::Height;
use ibc_relayer::chain::counterparty::pending_packet_summary;

use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

#[test]
fn test_query_packet_pending() -> Result<(), Error> {
    run_binary_channel_test(&QueryPacketPendingTest)
}

pub struct QueryPacketPendingTest;

impl TestOverrides for QueryPacketPendingTest {
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

impl BinaryChannelTest for QueryPacketPendingTest {
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

        let channel_end = chains.handle_a().query_channel(
            channel.port_a.as_ref().value(),
            channel.channel_id_a.as_ref().value(),
            Height::zero(),
        )?;
        let channel_end = IdentifiedChannelEnd::new(
            channel.port_a.clone().into_value(),
            channel.channel_id_a.clone().into_value(),
            channel_end,
        );

        let summary = pending_packet_summary(chains.handle_a(), chains.handle_b(), &channel_end)?;

        assert_eq!(summary.unreceived, [1]);
        // TODO: test pending_ack

        // Spawn the supervisor only after the first IBC trasnfer
        relayer.with_supervisor(|| {
            sleep(Duration::from_secs(1));

            Ok(())
        })
    }
}
