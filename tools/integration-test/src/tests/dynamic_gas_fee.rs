//! The [`DynamicGasTest`] test ensures that the [`DynamicGas`]
//! configuration works correctly.
//! It will first do an IBC transfer using the dynamic gas with a big memo
//! and record the gas used. It will then do a second IBC transfer but with
//! static gas and no memo and assert that the gas paid for the second transfer
//! is higher despite the big memo.
//!
//! The IBC transfer with dynamic gas contains a memo in order to reduce the
//! risks of false positive. Adding a memo will increase the gas price so if
//! the static gas price is used for the second transfer there is more chances
//! the assertion verifying that the second transfer was less costly.
//!
//! The [`StaticGasTest`] test ensures that the first IBC transfer will cost
//! more if dynamic gas is not configured.

use ibc_relayer::config::dynamic_gas::DynamicGas;
use ibc_relayer::config::{ChainConfig, GasPrice};
use ibc_test_framework::prelude::*;

#[test]
fn dynamic_gas_issue_example() -> Result<(), Error> {
    run_binary_channel_test(&DynamicGasTest2)
}

#[test]
fn test_dynamic_gas_transfer() -> Result<(), Error> {
    run_binary_channel_test(&DynamicGasTest)
}

#[test]
fn test_static_gas_transfer() -> Result<(), Error> {
    run_binary_channel_test(&StaticGasTest)
}

const MEMO_CHAR: &str = "a";
const MEMO_SIZE: usize = 10000;

pub struct DynamicGasTest2;

impl TestOverrides for DynamicGasTest2 {
    fn modify_relayer_config(&self, config: &mut Config) {
        for chain_config in config.chains.iter_mut() {
            chain_config.dynamic_gas = DynamicGas::unsafe_new(true, 1.1);
        }
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for DynamicGasTest2 {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let fee_denom_a = MonoTagged::new(Denom::base(&config.native_tokens[0]));

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

        warn!("transfer cli");

        let dst_height = chains.handle_b().query_latest_height()?;

        chains.node_a.chain_driver().transfer_from_chain(
            &chains.node_a.wallets().user1(),
            &chains.node_b.wallets().user1().address(),
            &channel.port_a.0,
            &channel.channel_id_a.0,
            &denom_a.with_amount(a_to_b_amount).as_ref(),
            &fee_denom_a.with_amount(1200u64).as_ref(),
            &dst_height,
        )?;

        warn!("supervisor spawn");
        // Do a simple IBC transfer with the dynamic gas configuration
        let paid_dynamic_gas = relayer.with_supervisor(|| {
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

            info!("IBC transfer with dynamic gas price was successful");

            Ok(paid_fees.unwrap())
        })?;

        warn!("paid fees {paid_dynamic_gas}");

        Ok(())
    }
}

pub struct DynamicGasTest;

impl TestOverrides for DynamicGasTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for DynamicGasTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let fee_denom_a = MonoTagged::new(Denom::base(&config.native_tokens[0]));

        let driver_a = chains.node_a.chain_driver().value().clone();

        // Create a separate chain driver to try and avoid the block_on panic.
        // And enable dynamic gas
        let mut modified_tx_config = driver_a.tx_config.clone();
        modified_tx_config.gas_config.dynamic_gas_price_multiplier = Some(1.1);

        let cd: MonoTagged<ChainA, ChainDriver> = MonoTagged::new(ChainDriver {
            chain_type: driver_a.chain_type.clone(),
            command_path: driver_a.command_path.clone(),
            chain_id: driver_a.chain_id.clone(),
            home_path: driver_a.home_path.clone(),
            account_prefix: driver_a.account_prefix.clone(),
            rpc_port: driver_a.rpc_port,
            grpc_port: driver_a.grpc_port,
            grpc_web_port: driver_a.grpc_web_port,
            p2p_port: driver_a.p2p_port,
            pprof_port: driver_a.pprof_port,
            tx_config: modified_tx_config,
            runtime: driver_a.runtime.clone(),
            compat_mode: driver_a.compat_mode.clone(),
        });

        // New relayer custom config
        let mut modified_config = relayer.config.clone();

        for chain_config in modified_config.chains.iter_mut() {
            chain_config.dynamic_gas = DynamicGas::unsafe_new(true, 1.1);
        }

        let r = RelayerDriver {
            config_path: relayer.config_path.clone(),
            config: modified_config,
            registry: relayer.registry.clone(),
            hang_on_fail: false,
        };
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

        warn!("transfer cli");

        let dst_height = chains.handle_b().query_latest_height()?;

        let memo: String = MEMO_CHAR.repeat(MEMO_SIZE);

        cd.as_ref().ibc_transfer_token_with_memo_and_timeout(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
            Some(memo),
            None,
        )?;

        warn!("supervisor spawn");
        // Do a simple IBC transfer with the dynamic gas configuration
        let paid_dynamic_gas = r.with_supervisor(|| {
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

            info!("IBC transfer with dynamic gas price was successful");

            Ok(paid_fees.unwrap())
        })?;

        warn!("paid fees {paid_dynamic_gas}");

        let mut modified_relayer = relayer.clone();

        // Disable dynamic gas configuration
        let new_chain_configs: Vec<ChainConfig> = modified_relayer
            .config
            .chains
            .iter_mut()
            .map(|c| {
                c.dynamic_gas = DynamicGas::unsafe_new(false, 0.9);
                c.clone()
            })
            .collect();

        modified_relayer.config.chains = new_chain_configs;

        let balance_user1_before = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &gas_denom.as_ref())?;

        chains.node_a.chain_driver().transfer_from_chain(
            &chains.node_a.wallets().user1(),
            &chains.node_b.wallets().user1().address(),
            &channel.port_a.0,
            &channel.channel_id_a.0,
            &denom_a.with_amount(a_to_b_amount).as_ref(),
            &fee_denom_a.with_amount(1200u64).as_ref(),
            &dst_height,
        )?;

        let paid_static_gas = relayer.with_supervisor(|| {
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

        warn!("First {paid_static_gas}, second {paid_dynamic_gas}");

        assert!(
            paid_static_gas > paid_dynamic_gas,
            "gas paid with dynamic gas configuration should be lower"
        );

        Ok(())
    }
}

pub struct StaticGasTest;

impl TestOverrides for StaticGasTest {
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

impl BinaryChannelTest for StaticGasTest {
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

        let balance_user1_before = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &gas_denom.as_ref())?;

        // Create a very big memo to increase the gas price of the second IBC transfer
        let memo: String = MEMO_CHAR.repeat(MEMO_SIZE);

        chains
            .node_a
            .chain_driver()
            .ibc_transfer_token_with_memo_and_timeout(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.as_ref(),
                &wallet_b.address(),
                &denom_a.with_amount(a_to_b_amount).as_ref(),
                Some(memo),
                None,
            )?;

        let paid_static_gas2 = relayer.with_supervisor(|| {
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

            info!("Second IBC transfer with static gas price was successful");

            Ok(paid_fees.unwrap())
        })?;

        warn!("First {paid_static_gas}, second {paid_static_gas2}");
        assert!(
            paid_static_gas < paid_static_gas2,
            "gas paid for first IBC transfer should be lower. First {paid_static_gas}, second {paid_static_gas2}"
        );

        Ok(())
    }
}
