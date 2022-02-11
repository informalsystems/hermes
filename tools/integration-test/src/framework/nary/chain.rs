use ibc_relayer::chain::handle::ChainHandle;

use super::node::{run_nary_node_test, NaryNodeTest};

use crate::bootstrap::nary::chain::boostrap_chains_with_nodes;
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::node::NodeConfigOverride;
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::DropChainHandle;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::single::node::FullNode;

pub fn run_nary_chain_test<Test, Overrides, const SIZE: usize>(test: &Test) -> Result<(), Error>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride + NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_nary_node_test(&RunNaryChainTest::new(test))
}

pub trait NaryChainTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error>;
}

pub struct RunNaryChainTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, Overrides, const SIZE: usize> NaryNodeTest<SIZE> for RunNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    fn run(&self, config: &TestConfig, nodes: [FullNode; SIZE]) -> Result<(), Error> {
        let (relayer, chains) = boostrap_chains_with_nodes(config, nodes, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let _supervisor = self.test.get_overrides().spawn_supervisor(&relayer);

        let _drop_handles = chains
            .chain_handles
            .iter()
            .map(|handle| DropChainHandle(handle.clone()))
            .collect::<Vec<_>>();

        self.test.run(config, relayer, chains)?;

        Ok(())
    }
}

impl<'a, Test, const SIZE: usize> RunNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunNaryChainTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
