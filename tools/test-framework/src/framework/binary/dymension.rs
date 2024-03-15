use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest, HasOverrides, TestConfigOverride};
use crate::framework::binary::node::{NodeConfigOverride, NodeGenesisOverride};
use crate::prelude::FullNode;
use crate::types::config::TestConfig;

/**
Runs a test case that implements [`InterchainSecurityChainTest`].
*/
pub fn run_binary_dymension_node_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: DymensionChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride + TestConfigOverride,
{
    run_basic_test(&RunDymensionChainTest { test })
}
pub trait DymensionChainTest {
    /// Test runner
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error>;
}

/**
 A wrapper type that lifts a test case that implements [`DymensionChainTest`]
 into a test case the implements [`BasicTest`].
*/
pub struct RunDymensionChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunDymensionChainTest<'a, Test>
where
    Test: DymensionChainTest,
{
    /// Create a new [`DymensionChainTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> BasicTest for RunDymensionChainTest<'a, Test>
where
    Test: DymensionChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        // Bootstrap provider
        let node_a = bootstrap_single_node(
            builder,
            "1",
            false,
            |config| self.test.get_overrides().modify_node_config(config),
            |genesis| self.test.get_overrides().modify_genesis_file(genesis),
            0,
        )?;

        node_a.chain_driver.create_rollapp("rollappevm_1234-1")?;
        node_a.chain_driver.create_sequencer("rollappevm_1234-1")?;

        let node_b = bootstrap_single_node(
            builder,
            "1",
            false,
            |config| self.test.get_overrides().modify_node_config(config),
            |genesis| self.test.get_overrides().modify_genesis_file(genesis),
            1,
        )?;

        let _node_process_a = node_a.process.clone();
        let _node_process_b = node_b.process.clone();

        self.test.run(config, node_a, node_b)?;

        Ok(())
    }
}

impl<'a, Test, Overrides> HasOverrides for RunDymensionChainTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
