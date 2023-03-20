use ibc_test_framework::framework::next::chain::{
    CanSpawnRelayer, HasContextId, HasTwoChains, HasTwoChannels, HasTwoNodes,
};
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    run_binary_channel_test(&IbcTransferTest)
}

/**
   Test that IBC token transfer can still work with a single
   chain that is connected to itself.
*/
#[test]
fn test_self_connected_ibc_transfer() -> Result<(), Error> {
    run_self_connected_binary_chain_test(&RunBinaryConnectionTest::new(&RunBinaryChannelTest::new(
        &RunWithSupervisor::new(&IbcTransferTest),
    )))
}

/**
   Run the IBC transfer test as an N-ary chain test case with SIZE=2.

   The work on N-ary chain is currently still work in progress, so we put
   this behind the "experimental" feature flag so that normal developers
   are not obligated to understand how this test works yet.
*/
#[test]
fn test_nary_ibc_transfer() -> Result<(), Error> {
    run_binary_as_nary_channel_test(&IbcTransferTest)
}

#[test]
fn test_self_connected_nary_ibc_transfer() -> Result<(), Error> {
    run_self_connected_nary_chain_test(&RunNaryConnectionTest::new(&RunNaryChannelTest::new(
        &RunBinaryAsNaryChannelTest::new(&IbcTransferTest),
    )))
}

impl TestOverrides for IbcTransferTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

pub struct IbcTransferTest;

impl BinaryChannelTest for IbcTransferTest {
    fn run<Context>(&self, _relayer: RelayerDriver, context: &Context) -> Result<(), Error>
    where
        Context: HasTwoChains + HasTwoChannels + HasTwoNodes + CanSpawnRelayer + HasContextId,
    {
        info!("Will run test with {}", context.context_id());
        let _res = context.spawn_relayer();

        let node_a = context.node_a();
        let node_b = context.node_b();

        let denom_a = node_a.denom();

        let wallet_a = node_a.wallets().user1().cloned();
        let wallet_b = node_b.wallets().user1().cloned();
        let wallet_c = node_a.wallets().user2().cloned();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_b_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            context.chain_a().id(),
            context.chain_b().id(),
            a_to_b_amount,
            denom_a
        );

        let channel = context.channel();

        node_a.chain_driver().ibc_transfer_token(
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

        info!(
            "Waiting for user on chain B to receive IBC transferred amount of {}",
            a_to_b_amount
        );

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_b_amount).as_ref(),
        )?;

        node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount).as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            context.chain_a().id(),
            context.chain_b().id(),
        );

        let balance_c = node_a
            .chain_driver()
            .query_balance(&wallet_c.address(), &denom_a)?;

        let b_to_a_amount = random_u128_range(500, a_to_b_amount);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {}",
            context.chain_b().id(),
            context.chain_a().id(),
            b_to_a_amount,
        );

        node_b.chain_driver().ibc_transfer_token(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_c.address(),
            &denom_b.with_amount(b_to_a_amount).as_ref(),
        )?;

        node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount - b_to_a_amount).as_ref(),
        )?;

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_c.address(),
            &(balance_c + b_to_a_amount).as_ref(),
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            context.chain_b().id(),
            context.chain_a().id(),
        );

        Ok(())
    }
}
