use crate::bootstrap::single::bootstrap_single_chain;
use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::types::single::node::RunningNode;

pub fn run_binary_node_test(test: impl BinaryNodeTest) -> Result<(), Error> {
    run_basic_test(RunBinaryNodeTest(test))
}

pub trait BinaryNodeTest {
    fn run(&self, node_a: RunningNode, node_b: RunningNode) -> Result<(), Error>;
}

pub struct RunBinaryNodeTest<Test>(pub Test);

impl<Test> BasicTest for RunBinaryNodeTest<Test>
where
    Test: BinaryNodeTest,
{
    fn run(&self, _config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let node_a = bootstrap_single_chain(builder)?;
        let node_b = bootstrap_single_chain(builder)?;

        self.0.run(node_a, node_b)?;

        Ok(())
    }
}
