/*!
   Constructs for running test cases with more than two full nodes,
   running without setting up the relayer.
*/

use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::{run_basic_test, BasicTest, TestConfigOverride};
use crate::framework::binary::node::{NodeConfigOverride, NodeGenesisOverride};
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;
use crate::util::array::try_into_array;

pub fn run_nary_node_test<Test, Overrides, const SIZE: usize>(test: &Test) -> Result<(), Error>
where
    Test: NaryNodeTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride + TestConfigOverride,
{
    run_basic_test(&RunNaryNodeTest { test })
}

/**
   This trait is implemented for test cases that need to have more than two
   full nodes running without the relayer being setup.

   The test case is given `SIZE` number of [`FullNode`]s which represents
   the running full nodes.

   Test writers can use this to implement more advanced test cases which
   require manual setup of the relayer, so that the relayer can be started
   and stopped at a suitable time within the test.
*/
pub trait NaryNodeTest<const SIZE: usize> {
    fn run(&self, config: &TestConfig, nodes: [FullNode; SIZE]) -> Result<(), Error>;
}

/**
   A wrapper type that lifts a test case that implements [`NaryNodeTest`]
   into a test case the implements [`BasicTest`].
*/
pub struct RunNaryNodeTest<'a, Test, const SIZE: usize> {
    pub test: &'a Test,
}

impl<'a, Test, Overrides, const SIZE: usize> BasicTest for RunNaryNodeTest<'a, Test, SIZE>
where
    Test: NaryNodeTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let mut nodes = Vec::new();
        let mut node_processes = Vec::new();

        for i in 0..SIZE {
            let node = bootstrap_single_node(
                builder,
                &format!("{}", i + 1),
                config.bootstrap_with_random_ids,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                i,
            )?;

            node_processes.push(node.process.clone());
            nodes.push(node);
        }

        self.test.run(config, try_into_array(nodes)?)?;

        Ok(())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunNaryNodeTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
