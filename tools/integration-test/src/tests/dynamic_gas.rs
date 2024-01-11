use ibc_relayer::config::dynamic_gas::DynamicGas;
use ibc_relayer::config::{ChainConfig, GasPrice};
use ibc_test_framework::prelude::*;

#[test]
fn test_dynamic_gas_transfer() -> Result<(), Error> {
    run_binary_channel_test(&DynamicGasTest)
}

pub struct DynamicGasTest;

impl TestOverrides for DynamicGasTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Set a high gas price when not using dynamic gas price
        // in order to assert that dynamic gas price works correcly
        let _ = config.chains.iter_mut().map(|c| {
            c.gas_price = GasPrice::new(0.1, c.gas_price.denom.clone());
        });
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for DynamicGasTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let a_to_b_amount = 12345u64;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let gas_denom: MonoTagged<ChainA, Denom> = MonoTagged::new(Denom::Base("stake".to_owned()));

        let balance_user1_before = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &gas_denom.as_ref())?;

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        // Do a simple IBC transfer without the dynamic gas configuration
        let paid_static_gas = relayer.with_supervisor(|| {
            // Assert that user on chain B received the tokens
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b.with_amount(a_to_b_amount).as_ref(),
            )?;

            let balance_after_a1 = chains.node_a.chain_driver().query_balance(
                &chains.node_a.wallets().user1().address(),
                &gas_denom.as_ref(),
            )?;

            let paid_fees = balance_user1_before
                .amount()
                .checked_sub(balance_after_a1.amount());

            assert!(
                paid_fees.is_some(),
                "subtraction between queried amounts should be Some"
            );

            info!("IBC transfer with static gas price was successful");

            Ok(paid_fees.unwrap())
        })?;

        let mut modified_relayer = relayer;

        // Set dynamic gas configuration
        let new_chain_configs: Vec<ChainConfig> = modified_relayer
            .config
            .chains
            .iter_mut()
            .map(|c| {
                if c.id == chains.node_a.chain_id().0.clone() {
                    c.dynamic_gas_price = DynamicGas::unsafe_new(true, 1.1);
                }
                c.clone()
            })
            .collect();

        modified_relayer.config.chains = new_chain_configs;

        let balance_user1_before = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &gas_denom.as_ref())?;

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        let paid_dynamic_gas = modified_relayer.with_supervisor(|| {
            // Assert that user on chain B received the tokens
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b.with_amount(a_to_b_amount + a_to_b_amount).as_ref(),
            )?;

            let balance_after_a1 = chains.node_a.chain_driver().query_balance(
                &chains.node_a.wallets().user1().address(),
                &gas_denom.as_ref(),
            )?;

            let paid_fees = balance_user1_before
                .amount()
                .checked_sub(balance_after_a1.amount());

            assert!(
                paid_fees.is_some(),
                "subtraction between queried amounts should be Some"
            );

            info!("IBC transfer with dynamic gas price was successful");

            Ok(paid_fees.unwrap())
        })?;

        assert!(
            paid_static_gas > paid_dynamic_gas,
            "gas paid with dynamic gas configuration should be lower"
        );

        Ok(())
    }
}
