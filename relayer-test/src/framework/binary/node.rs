/*!
   Constructs for running test cases with two full nodes
   running without setting up the relayer.
*/

use crate::bootstrap::single::bootstrap_single_chain;
use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::types::single::node::RunningNode;

/**
   Runs a test case that implements [`BinaryNodeTest`].
*/
pub fn run_binary_node_test<Test: BinaryNodeTest>(test: &Test) -> Result<(), Error> {
    run_owned_binary_node_test(&RunBinaryNodeTest { test })
}

/**
   Runs a test case that implements [`OwnedBinaryNodeTest`].
*/
pub fn run_owned_binary_node_test<Test: OwnedBinaryNodeTest>(test: &Test) -> Result<(), Error> {
    run_basic_test(&RunOwnedBinaryNodeTest { test })
}

/**
   This trait is implemented for test cases that need to have two full nodes
   running without the relayer being setup.

   The test case is given two references to [`RunningNode`] which represents
   the two running full nodes.

   Test writers can use this to implement more advanced test cases which
   require manual setup of the relayer, so that the relayer can be started
   and stopped at a suitable time within the test.
*/
pub trait BinaryNodeTest {
    fn run(
        &self,
        config: &TestConfig,
        node_a: &RunningNode,
        node_b: &RunningNode,
    ) -> Result<(), Error>;
}

/**
   An owned version of [`BinaryNodeTest`], which the test case is given owned
   [`RunningNode`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   be stopped at the end of the test case. The test framework cannot use
   functions such as [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
*/
pub trait OwnedBinaryNodeTest {
    fn run(
        &self,
        config: &TestConfig,
        node_a: RunningNode,
        node_b: RunningNode,
    ) -> Result<(), Error>;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryNodeTest`]
   into a test case the implements [`OwnedBinaryNodeTest`].
*/
pub struct RunBinaryNodeTest<'a, Test> {
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`OwnedBinaryNodeTest`]
   into a test case that implements [`BasicTest`].
*/
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
