//! The following tests are for the Interchain Security.
//! These tests require the first chain to be a Producer chain and
//! the second chain a Consumer chain.
use ibc_test_framework::chain::config::set_voting_period;
use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_ics_transfer() -> Result<(), Error> {
    run_binary_interchain_security_channel_test(&InterchainSecurityTransferTest)
}

struct InterchainSecurityTransferTest;

impl TestOverrides for InterchainSecurityTransferTest {
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        // Consumer chain doesn't have a gov key.
        if genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get("gov"))
            .is_some()
        {
            set_voting_period(genesis, "10s")?;
        }
        Ok(())
    }

    // The `ccv_consumer_chain` must be `true` for the Consumer chain.
    // The `trusting_period` must be strictly smaller than the `unbonding_period`
    // specified in the Consumer chain proposal. The test framework uses 100s in
    // the proposal.
    fn modify_relayer_config(&self, config: &mut Config) {
        for chain_config in config.chains.iter_mut() {
            if chain_config.id == ChainId::from_string("ibcconsumer") {
                chain_config.ccv_consumer_chain = true;
                chain_config.trusting_period = Some(Duration::from_secs(99));
            }
        }
    }
}

impl BinaryChannelTest for InterchainSecurityTransferTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();
        let wallet_c = chains.node_a.wallets().user2().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_b_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with: channel id {}, port id {} and amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            channel.channel_id_a.to_string(),
            channel.port_a.to_string(),
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

        info!(
            "Waiting for user on chain B to receive IBC transferred amount of {}",
            a_to_b_amount
        );

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a - a_to_b_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount).as_ref(),
        )?;

        info!(
            "successfully performed IBC transfer from chain {} to chain {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        let balance_c = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_c.address(), &denom_a)?;

        let b_to_a_amount = random_u128_range(500, a_to_b_amount);

        info!(
            "Sending IBC transfer from chain {} to chain {} with: channel id {}, port id {} and amount of {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
            channel.channel_id_b.to_string(),
            channel.port_b.to_string(),
            b_to_a_amount,
        );

        chains.node_b.chain_driver().ibc_transfer_token(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_c.address(),
            &denom_b.with_amount(b_to_a_amount).as_ref(),
        )?;

        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            &denom_b.with_amount(a_to_b_amount - b_to_a_amount).as_ref(),
        )?;

        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_c.address(),
            &(balance_c + b_to_a_amount).as_ref(),
        )?;

        info!(
            "successfully performed reverse IBC transfer from chain {} back to chain {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
        );
        Ok(())
    }
}
