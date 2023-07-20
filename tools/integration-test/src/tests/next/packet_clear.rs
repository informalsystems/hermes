use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_components_extra::packet_clear::traits::packet_clear::CanClearReceivePackets;
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

        let relay_context = build_cosmos_relay_context(&relayer.config, chains, pf.clone())?;
        let relay_context2 = build_cosmos_relay_context(&relayer.config, chains, pf)?;

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

        runtime.spawn(async move {
            let _ = relay_context
                .relay_b_to_a()
                .clear_receive_packets(
                    channel.channel_id_b.value(),
                    channel.port_b.value(),
                    channel.channel_id_a.value(),
                    channel.port_a.value(),
                )
                .await;
        });

        sleep(Duration::from_secs(10));

        info!("Clear packets from B to A should not clear the pending packet from A to B");

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a.clone() - a_to_b_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(0u64).as_ref(),
        )?;

        runtime.spawn(async move {
            let _ = relay_context2
                .relay_a_to_b()
                .clear_receive_packets(
                    cloned_channel.channel_id_b.value(),
                    cloned_channel.port_b.value(),
                    cloned_channel.channel_id_a.value(),
                    cloned_channel.port_a.value(),
                )
                .await;
        });

        info!("Clear packet from A to B should clear the pending packet");

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_b_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount).as_ref(),
        )?;

        sleep(Duration::from_secs(2));

        Ok(())
    }
}
