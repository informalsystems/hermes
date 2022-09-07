use ibc_relayer_framework::core::impls::packet_relayers::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use ibc_relayer_framework::core::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
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
        let relay_context = build_cosmos_relay_context(&chains);
        let relayer = BaseTimeoutUnorderedPacketRelayer;

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

        let chain_a_height = chains.handle_a.query_latest_height().unwrap();
        let chain_a_height = chain_a_height.decrement().unwrap();

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

        runtime.block_on(async {
            relayer
                .relay_timeout_unordered_packet(&relay_context, &chain_a_height, &packet)
                .await
                .unwrap()
        });

        info!("finished running relayer");

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            balance_a,
            &denom_a,
        )?;

        // chains.node_b.chain_driver().assert_eventual_wallet_amount(
        //     &wallet_b.address(),
        //     balance_b,
        //     &denom_b.as_ref(),
        // )?;

        // info!(
        //     "successfully performed IBC transfer from chain {} to chain {}",
        //     chains.chain_id_a(),
        //     chains.chain_id_b(),
        // );

        Ok(())
    }
}
