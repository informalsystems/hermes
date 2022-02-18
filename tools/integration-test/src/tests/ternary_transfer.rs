use crate::ibc::denom::derive_ibc_denom;
use crate::prelude::*;
use crate::util::random::random_u64_range;

#[test]
fn test_ternary_ibc_transfer() -> Result<(), Error> {
    run_nary_channel_test(&TernaryIbcTransferTest)
}

pub struct TernaryIbcTransferTest;

impl TestOverrides for TernaryIbcTransferTest {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.clients.misbehaviour = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl PortsOverride<3> for TernaryIbcTransferTest {}

impl NaryChannelTest<3> for TernaryIbcTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        let _handle = relayer.spawn_supervisor()?;

        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;

        let denom_a = node_a.denom();

        let wallet_a1 = node_a.wallets().user1().cloned();
        let wallet_a2 = node_a.wallets().user2().cloned();

        let wallet_b1 = node_b.wallets().user1().cloned();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a1.address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        let channel_a_to_b = channels.channel_at::<0, 1>()?;

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            node_a.chain_id(),
            node_b.chain_id(),
            a_to_b_amount,
            denom_a
        );

        node_a.chain_driver().transfer_token(
            &channel_a_to_b.port_a.as_ref(),
            &channel_a_to_b.channel_id_a.as_ref(),
            &wallet_a1.address(),
            &wallet_b1.address(),
            a_to_b_amount,
            &denom_a,
        )?;

        let denom_b = derive_ibc_denom(
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "Waiting for user on chain B to receive IBC transferred amount of {} {}",
            a_to_b_amount, denom_b
        );

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a1.as_ref(),
            balance_a - a_to_b_amount,
            &denom_a,
        )?;

        node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b1.as_ref(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

        // info!(
        //     "successfully performed IBC transfer from chain {} to chain {}",
        //     chains.chain_id_a(),
        //     chains.chain_id_b(),
        // );

        // let balance_c = chains
        //     .node_a
        //     .chain_driver()
        //     .query_balance(&wallet_c.address(), &denom_a)?;

        // let b_to_a_amount = random_u64_range(500, a_to_b_amount);

        // info!(
        //     "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
        //     chains.chain_id_b(),
        //     chains.chain_id_a(),
        //     b_to_a_amount,
        //     denom_b
        // );

        // chains.node_b.chain_driver().transfer_token(
        //     &channel.port_b.as_ref(),
        //     &channel.channel_id_b.as_ref(),
        //     &wallet_b.address(),
        //     &wallet_c.address(),
        //     b_to_a_amount,
        //     &denom_b.as_ref(),
        // )?;

        // chains.node_b.chain_driver().assert_eventual_wallet_amount(
        //     &wallet_b.as_ref(),
        //     a_to_b_amount - b_to_a_amount,
        //     &denom_b.as_ref(),
        // )?;

        // chains.node_a.chain_driver().assert_eventual_wallet_amount(
        //     &wallet_c.as_ref(),
        //     balance_c + b_to_a_amount,
        //     &denom_a,
        // )?;

        // info!(
        //     "successfully performed reverse IBC transfer from chain {} back to chain {}",
        //     chains.chain_id_b(),
        //     chains.chain_id_a(),
        // );

        Ok(())
    }
}
