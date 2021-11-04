use crate::bootstrap::single::bootstrap_single_chain;
use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::types::single::node::RunningNode;

pub fn run_binary_node_test<Test: BinaryNodeTest>(test: &Test) -> Result<(), Error> {
    run_owned_binary_node_test(&RunBinaryNodeTest { test })
}

pub fn run_owned_binary_node_test<Test: OwnedBinaryNodeTest>(test: &Test) -> Result<(), Error> {
    run_basic_test(&RunOwnedBinaryNodeTest { test })
}

pub trait BinaryNodeTest {
    fn run(
        &self,
        config: &TestConfig,
        node_a: &RunningNode,
        node_b: &RunningNode,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryNodeTest {
    fn run(
        &self,
        config: &TestConfig,
        node_a: RunningNode,
        node_b: RunningNode,
    ) -> Result<(), Error>;
}

pub struct RunBinaryNodeTest<'a, Test> {
    pub test: &'a Test,
}

pub struct RunOwnedBinaryNodeTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test> BasicTest for RunOwnedBinaryNodeTest<'a, Test>
where
    Test: OwnedBinaryNodeTest,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let node_a = bootstrap_single_chain(builder, "alpha")?;
        let node_b = bootstrap_single_chain(builder, "beta")?;

        self.test.run(config, node_a, node_b)?;

        // No use hanging the test on owned failures, as the nodes
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<'a, Test> OwnedBinaryNodeTest for RunBinaryNodeTest<'a, Test>
where
    Test: BinaryNodeTest,
{
    fn run(
        &self,
        config: &TestConfig,
        node_a: RunningNode,
        node_b: RunningNode,
    ) -> Result<(), Error> {
        self.test
            .run(config, &node_a, &node_b)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}
