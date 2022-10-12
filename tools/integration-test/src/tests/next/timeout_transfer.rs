//! This test ensures that a source chain that initiates an IBC transfer is
//! refunded the tokens that it sent in response to receiving a timeout packet.
//!
//! It sets up a Cosmos relay context, a [`BaseTimeoutUnorderedPacketRelayer`],
//! a chain runtime, and two wallets, `wallet_a` and `wallet_b`. An IBC token
//! transfer is initiated. Afterwards, a timeout packet is sent from the chain
//! that received the token transfer to the chain that initiated it. Finally,
//! it checks that the source chain's wallet balance has been restored to its
//! original amount before the transfer was initiated.

use ibc_relayer::config::PacketFilter;

use ibc_relayer_framework::base::impls::packet_relayers::base_timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_framework::base::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
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
            &denom_a,
            a_to_b_amount,
            Some(Duration::from_secs(1)),
        )?;

        info!("running relayer");

        sleep(Duration::from_secs(5));

        let chain_b_height = chains.handle_b.query_latest_height().unwrap();
        let chain_b_height = chain_b_height.decrement().unwrap();

        runtime.block_on(async {
            BaseTimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
                &relay_context,
                &chain_b_height,
                &packet,
            )
            .await
            .unwrap()
        });

        info!("finished running relayer");

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            balance_a,
            &denom_a,
        )?;

        info!(
            "successfully refunded IBC transfer back to chain {} from chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        Ok(())
    }
}
