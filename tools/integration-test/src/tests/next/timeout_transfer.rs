//! Tests the capability of a full relayer instance to relay a timeout packet.
//!
//! This test ensures that a source chain that initiates an IBC transfer is
//! refunded the tokens that it sent in response to receiving a timeout packet
//! relayed by a full relayer.

use ibc_relayer::config::PacketFilter;
use ibc_relayer_components::relay::traits::components::packet_relayer::CanRelayPacket;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_test_framework::framework::next::chain::{HasTwoChains, HasTwoChannels};
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_ibc_transfer_timeout_next() -> Result<(), Error> {
    run_binary_channel_test(&IbcTransferTest)
}

pub struct IbcTransferTest;

impl TestOverrides for IbcTransferTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IbcTransferTest {
    fn run<Context>(&self, relayer: RelayerDriver, context: &Context) -> Result<(), Error>
    where
        Context: HasTwoChains + HasTwoChannels,
    {
        let chains = context.chains();
        let channel = context.channel();
        let pf: PacketFilter = PacketFilter::default();

        let relay_context = build_cosmos_relay_context(&relayer.config, chains, pf)?;

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
            "Sending IBC timeout from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        let packet = chains
            .node_a
            .chain_driver()
            .ibc_transfer_token_with_memo_and_timeout(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.as_ref(),
                &wallet_b.address(),
                &denom_a.with_amount(a_to_b_amount).as_ref(),
                None,
                Some(Duration::from_secs(1)),
            )?;

        info!("running relayer");

        sleep(Duration::from_secs(5));

        runtime.block_on(async {
            relay_context
                .relay_a_to_b()
                .relay_packet(&packet)
                .await
                .unwrap()
        });

        info!("finished running relayer");

        chains
            .node_a
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_a.address(), &balance_a.as_ref())?;

        info!(
            "successfully refunded IBC transfer back to chain {} from chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        Ok(())
    }
}
