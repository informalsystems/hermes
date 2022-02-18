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
        relayer.with_supervisor(|| {
            let node_a = chains.full_node_at::<0>()?;
            let node_b = chains.full_node_at::<1>()?;
            let node_c = chains.full_node_at::<2>()?;

            let denom_a = node_a.denom();

            let wallet_a1 = node_a.wallets().user1().cloned();

            let wallet_b1 = node_b.wallets().user1().cloned();

            let wallet_c1 = node_c.wallets().user1().cloned();

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

            info!(
                "successfully performed IBC transfer from chain {} to chain {}",
                node_a.chain_id(),
                node_b.chain_id(),
            );

            let channel_b_to_c = channels.channel_at::<1, 2>()?;

            let denom_c = derive_ibc_denom(
                &channel_b_to_c.port_b.as_ref(),
                &channel_b_to_c.channel_id_b.as_ref(),
                &denom_b.as_ref(),
            )?;

            let b_to_c_amount = random_u64_range(500, a_to_b_amount);

            node_b.chain_driver().transfer_token(
                &channel_b_to_c.port_a.as_ref(),
                &channel_b_to_c.channel_id_a.as_ref(),
                &wallet_b1.address(),
                &wallet_c1.address(),
                b_to_c_amount,
                &denom_b.as_ref(),
            )?;

            info!(
                "Waiting for user on chain C to receive IBC transferred amount of {} {}",
                b_to_c_amount, denom_c
            );

            info!("waiting for chain B balance to decrease");

            node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b1.as_ref(),
                a_to_b_amount - b_to_c_amount,
                &denom_b.as_ref(),
            )?;

            info!("waiting for chain C balance to increase");

            node_c.chain_driver().assert_eventual_wallet_amount(
                &wallet_c1.as_ref(),
                b_to_c_amount,
                &denom_c.as_ref(),
            )?;

            Ok(())
        })
    }
}
