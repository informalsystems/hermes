/*!
   Constructs for running test cases with two full nodes
   running without setting up the relayer.
*/

use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;

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

   The test case is given two references to [`FullNode`] which represents
   the two running full nodes.

   Test writers can use this to implement more advanced test cases which
   require manual setup of the relayer, so that the relayer can be started
   and stopped at a suitable time within the test.
*/
pub trait BinaryNodeTest {
    /// Test runner
    fn run(&self, config: &TestConfig, node_a: &FullNode, node_b: &FullNode) -> Result<(), Error>;
}

/**
   An owned version of [`BinaryNodeTest`], which the test case is given owned
   [`FullNode`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   be stopped at the end of the test case. The test framework cannot use
   functions such as [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
*/
pub trait OwnedBinaryNodeTest {
    /// Test runner
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error>;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryNodeTest`]
   into a test case the implements [`OwnedBinaryNodeTest`].
*/
pub struct RunBinaryNodeTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`OwnedBinaryNodeTest`]
   into a test case that implements [`BasicTest`].
*/
pub struct RunOwnedBinaryNodeTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> BasicTest for RunOwnedBinaryNodeTest<'a, Test>
where
    Test: OwnedBinaryNodeTest,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let node_a = bootstrap_single_node(builder, "alpha")?;
        let node_b = bootstrap_single_node(builder, "beta")?;

        self.test.run(config, node_a, node_b)?;

        // No use suspending the test on owned failures, as the nodes
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<'a, Test> OwnedBinaryNodeTest for RunBinaryNodeTest<'a, Test>
where
    Test: BinaryNodeTest,
{
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error> {
        self.test
            .run(config, &node_a, &node_b)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}
