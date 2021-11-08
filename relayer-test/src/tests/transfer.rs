use crate::ibc::denom::derive_ibc_denom;
use crate::prelude::*;
use crate::util::random::random_u64_range;

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    run_two_way_binary_channel_test(&IbcTransferTest)
}

pub struct IbcTransferTest;

impl TestOverrides for IbcTransferTest {}

impl BinaryChannelTest for IbcTransferTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
        channel: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let chaina_user1_balance = chains
            .node_a
            .chain_driver()
            .query_balance(&chains.node_a.wallets().user1().address(), &denom_a)?;

        let a_to_b_amount = random_u64_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().transfer_token(
            &channel.port_a,
            &channel.channel_id_a,
            &chains.node_a.wallets().user1().address(),
            &chains.node_b.wallets().user1().address(),
            a_to_b_amount,
            &denom_a,
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!(
            "Waiting for user on chain B to receive IBC transferred amount of {} {}",
            a_to_b_amount, denom_b
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &chains.node_a.wallets().user1(),
            chaina_user1_balance - a_to_b_amount,
            &denom_a,
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &chains.node_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        let chaina_user2_balance = chains
            .node_a
            .chain_driver()
            .query_balance(&chains.node_a.wallets().user2().address(), &denom_a)?;

        let b_to_a_amount = random_u64_range(500, a_to_b_amount);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
            b_to_a_amount,
            denom_b
        );

        chains.node_b.chain_driver().transfer_token(
            &channel.port_b,
            &channel.channel_id_b,
            &chains.node_b.wallets().user1().address(),
            &chains.node_a.wallets().user2().address(),
            b_to_a_amount,
            &denom_b.as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &chains.node_b.wallets().user1(),
            a_to_b_amount - b_to_a_amount,
            &denom_b.as_ref(),
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &chains.node_a.wallets().user2(),
            chaina_user2_balance + b_to_a_amount,
            &denom_a,
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
        );

        Ok(())
    }
}
