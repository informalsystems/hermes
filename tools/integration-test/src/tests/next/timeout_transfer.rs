//! Tests the capability of a full relayer instance to relay a timeout packet.
//!
//! This test ensures that a source chain that initiates an IBC transfer is
//! refunded the tokens that it sent in response to receiving a timeout packet
//! relayed by a full relayer.

use ibc_relayer::config::PacketFilter;

use ibc_relayer_framework::base::relay::traits::packet_relayer::CanRelayPacket;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use crate::tests::next::context::build_cosmos_relay_context;

#[test]
fn test_ibc_transfer_next() -> Result<(), Error> {
    run_binary_channel_test(&IbcTransferTest)
}

pub struct IbcTransferTest;

impl TestOverrides for IbcTransferTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IbcTransferTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let pf: PacketFilter = PacketFilter::AllowAll;

        let relay_context = build_cosmos_relay_context(&chains, pf);

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

        let packet = chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
            Some(Duration::from_secs(1)),
        )?;

        info!("running relayer");

        sleep(Duration::from_secs(5));

        runtime.block_on(async { relay_context.relay_packet(&packet).await.unwrap() });

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
