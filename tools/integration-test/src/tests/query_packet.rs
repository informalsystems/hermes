use ibc_relayer::chain::counterparty::{channel_on_destination, pending_packet_summary};
use ibc_relayer::link::{Link, LinkParameters};

use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::query_identified_channel_end;
use ibc_test_framework::relayer::connection::query_identified_connection_end;
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
}

impl BinaryChannelTest for QueryPacketPendingTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
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

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a,
            amount1,
        )?;

        sleep(Duration::from_secs(2));

        let opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.into_value(),
        };
        let link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            opts,
            false,
        )?;

        let channel_end = query_identified_channel_end(
            chains.handle_a(),
            channel.channel_id_a.as_ref(),
            channel.port_a.as_ref(),
        )?;

        let summary =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end.value())?;

        assert_eq!(summary.unreceived_packets, [1.into()]);
        assert!(summary.unreceived_acks.is_empty());

        // Receive the packet on the destination chain
        link.relay_recv_packet_and_timeout_messages()?;

        let summary =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end.value())?;

        assert!(summary.unreceived_packets.is_empty());
        assert_eq!(summary.unreceived_acks, [1.into()]);

        // Acknowledge the packet on the source chain
        let link = link.reverse(false)?;
        link.relay_ack_packet_messages()?;

        let summary =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end.value())?;

        assert!(summary.unreceived_packets.is_empty());
        assert!(summary.unreceived_acks.is_empty());

        let denom_b = chains.node_b.denom();
        let amount2 = random_u64_range(1000, 5000);

        chains.node_b.chain_driver().ibc_transfer_token(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &denom_b,
            amount2,
        )?;

        info!(
            "Performing IBC transfer with amount {}, which should *not* be relayed",
            amount2
        );

        sleep(Duration::from_secs(2));

        // Get the reverse channel end, like the CLI command does
        let connection_end = query_identified_connection_end(
            chains.handle_a(),
            channel.connection.connection_id_a.as_ref(),
        )?;
        let counterparty_channel_end = channel_on_destination(
            channel_end.value(),
            connection_end.value(),
            chains.handle_b(),
        )?
        .unwrap();

        let summary = pending_packet_summary(
            chains.handle_b(),
            chains.handle_a(),
            &counterparty_channel_end,
        )?;

        assert_eq!(summary.unreceived_packets, [1.into()]);
        assert!(summary.unreceived_acks.is_empty());

        Ok(())
    }
}
