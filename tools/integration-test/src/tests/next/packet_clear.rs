use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use ibc_relayer_components::chain::traits::queries::send_packet::CanQuerySendPacketsFromSequences;
use ibc_relayer_components::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPacketSequences;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::clear_packet::CanClearPackets;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::Height;
use ibc_test_framework::framework::next::chain::{HasTwoChains, HasTwoChannels};
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_ibc_clear_packet_next() -> Result<(), Error> {
    run_binary_channel_test(&IbcClearPacketTest)
}

pub struct IbcClearPacketTest;

impl TestOverrides for IbcClearPacketTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IbcClearPacketTest {
    fn run<Context>(&self, relayer: RelayerDriver, context: &Context) -> Result<(), Error>
    where
        Context: HasTwoChains + HasTwoChannels,
    {
        let chains = context.chains();
        let cloned_channel = context.channel().clone();
        let channel = context.channel().clone();
        let pf: PacketFilter = PacketFilter::default();

        let relay_context = build_cosmos_relay_context(&relayer.config, chains, pf)?;

        let relay_a_to_b = relay_context.relay_a_to_b();
        let relay_b_to_a = relay_context.relay_b_to_a();
        let chain_a = relay_a_to_b.src_chain();
        let chain_b = relay_a_to_b.dst_chain();

        let runtime = chains.node_a.value().chain_driver.runtime.as_ref();

        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        runtime.block_on(async {
            info!("Assert query packet commitments works as expected");

            let (src_commitments, src_height): (Vec<Sequence>, Height) = chain_a
                .query_packet_commitments(channel.channel_id_a.value(), channel.port_a.value())
                .await
                .unwrap();

            assert_eq!(src_commitments, vec!(Sequence::from(1)));

            let (dst_commitments, dst_height): (Vec<Sequence>, Height) = chain_b
                .query_packet_commitments(channel.channel_id_b.value(), channel.port_b.value())
                .await
                .unwrap();

            assert_eq!(dst_commitments, vec!());

            info!("Assert query unreceived packet sequences works as expected");

            let unreceived_packet_sequences: Vec<Sequence> = chain_a
                .query_unreceived_packet_sequences(
                    channel.channel_id_a.value(),
                    channel.port_a.value(),
                    &src_commitments,
                )
                .await
                .unwrap();

            assert_eq!(unreceived_packet_sequences, vec!(Sequence::from(1)));

            let unreceived_packet_sequences: Vec<Sequence> = chain_b
                .query_unreceived_packet_sequences(
                    channel.channel_id_b.value(),
                    channel.port_b.value(),
                    &src_commitments,
                )
                .await
                .unwrap();

            assert_eq!(unreceived_packet_sequences, vec!(Sequence::from(1)));

            info!("Assert query unreceived packets works as expected");

            let send_packets = chain_a
                .query_send_packets_from_sequences(
                    channel.channel_id_a.value(),
                    channel.port_a.value(),
                    channel.channel_id_b.value(),
                    channel.port_b.value(),
                    &unreceived_packet_sequences,
                    &src_height,
                )
                .await
                .unwrap();

            assert_eq!(send_packets.len(), 1);

            let send_packets = chain_b
                .query_send_packets_from_sequences(
                    channel.channel_id_b.value(),
                    channel.port_b.value(),
                    channel.channel_id_a.value(),
                    channel.port_a.value(),
                    &unreceived_packet_sequences,
                    &dst_height,
                )
                .await;

            assert!(
                send_packets.is_err(),
                "There should be no send packets from Chain B"
            );

            let _ = relay_b_to_a
                .clear_packets(
                    channel.channel_id_a.value(),
                    channel.port_a.value(),
                    channel.channel_id_b.value(),
                    channel.port_b.value(),
                )
                .await;

            info!("Clear packets from B to A should not clear the pending packet from A to B");

            let amount = chains
                .node_a
                .chain_driver()
                .query_balance(&wallet_a.address(), &balance_a.denom())
                .unwrap();

            assert_eq!(
                amount.value().amount,
                (balance_a.clone() - a_to_b_amount).amount()
            );

            let amount = chains
                .node_b
                .chain_driver()
                .query_balance(&wallet_b.address(), &denom_b.as_ref())
                .unwrap();

            assert_eq!(amount.value().amount, denom_b.with_amount(0u64).amount());

            let _ = relay_a_to_b
                .clear_packets(
                    cloned_channel.channel_id_a.value(),
                    cloned_channel.port_a.value(),
                    cloned_channel.channel_id_b.value(),
                    cloned_channel.port_b.value(),
                )
                .await;

            info!("Clear packet from A to B should clear the pending packet");

            let amount = chains
                .node_a
                .chain_driver()
                .query_balance(&wallet_a.address(), &balance_a.denom())
                .unwrap();

            assert_eq!(
                amount.value().amount,
                (balance_a.clone() - a_to_b_amount).amount()
            );

            let amount = chains
                .node_b
                .chain_driver()
                .query_balance(&wallet_b.address(), &denom_b.as_ref())
                .unwrap();

            assert_eq!(
                amount.value().amount,
                denom_b.with_amount(a_to_b_amount).amount()
            );
        });

        Ok(())
    }
}
