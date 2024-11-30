use std::str::FromStr;
use std::thread;

use crate::bootstrap::consumer::bootstrap_consumer_node;
use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::chain::chain_type::ChainType;
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest, HasOverrides, TestConfigOverride};
use crate::framework::binary::node::{NodeConfigOverride, NodeGenesisOverride};
use crate::prelude::FullNode;
use crate::types::config::TestConfig;

/**
Runs a test case that implements [`InterchainSecurityChainTest`].
*/
pub fn run_binary_interchain_security_node_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: InterchainSecurityChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride + TestConfigOverride,
{
    run_basic_test(&RunInterchainSecurityChainTest { test })
}
pub trait InterchainSecurityChainTest {
    /// Test runner
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error>;
}

/**
 A wrapper type that lifts a test case that implements [`InterchainSecurityChainTest`]
 into a test case the implements [`BasicTest`].
*/
pub struct RunInterchainSecurityChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunInterchainSecurityChainTest<'a, Test>
where
    Test: InterchainSecurityChainTest,
{
    /// Create a new [`InterchainSecurityChainTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<Test, Overrides> BasicTest for RunInterchainSecurityChainTest<'_, Test>
where
    Test: InterchainSecurityChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        // Bootstrap provider
        let node_a = bootstrap_single_node(
            builder,
            "provider",
            false,
            |config| self.test.get_overrides().modify_node_config(config),
            |genesis| self.test.get_overrides().modify_genesis_file(genesis),
            0,
        )?;
        let provider_native_token = builder.native_tokens[0].clone();
        let provider_fee = format!("381000000{provider_native_token}");

        // Get consumer chain id
        let chain_type = ChainType::from_str(&builder.command_paths[1])?;
        let chain_id = chain_type.chain_id("consumer", false);

        let consumer_id = node_a
            .chain_driver
            .create_permisionless_consumer(chain_id.as_str(), &provider_fee)?;

        thread::sleep(std::time::Duration::from_secs(3));

        node_a.chain_driver.update_consumer(
            &consumer_id,
            &provider_fee,
            node_a.wallets.validator.address.as_str(),
        )?;

        thread::sleep(std::time::Duration::from_secs(3));

        let node_b = bootstrap_consumer_node(
            builder,
            &consumer_id,
            &node_a,
            |config| self.test.get_overrides().modify_node_config(config),
            |genesis| self.test.get_overrides().modify_genesis_file(genesis),
            1,
            &node_a.chain_driver,
            &provider_fee,
        )?;

        let _node_process_a = node_a.process.clone();
        let _node_process_b = node_b.process.clone();

        self.test.run(config, node_a, node_b)?;

        Ok(())
    }
}

impl<Test, Overrides> HasOverrides for RunInterchainSecurityChainTest<'_, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
