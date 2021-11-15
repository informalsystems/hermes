use ibc_relayer::chain::handle::ChainHandle;

use super::node::{run_owned_nary_node_test, OwnedNaryNodeTest};

use crate::bootstrap::nary::chain::boostrap_chains_with_nodes;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::node::NodeConfigOverride;
use crate::types::binary::chains::DropChainHandle;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::single::node::FullNode;

pub fn run_owned_nary_chain_test<Test, Overrides, const SIZE: usize>(
    test: &Test,
) -> Result<(), Error>
where
    Test: OwnedNaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_owned_nary_node_test(&RunOwnedNaryChainTest::new(test))
}

pub trait OwnedNaryChainTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error>;
}

pub struct RunOwnedNaryChainTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, Overrides, const SIZE: usize> OwnedNaryNodeTest<SIZE>
    for RunOwnedNaryChainTest<'a, Test, SIZE>
where
    Test: OwnedNaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    fn run(&self, config: &TestConfig, nodes: [FullNode; SIZE]) -> Result<(), Error> {
        let chains = boostrap_chains_with_nodes(config, nodes, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let _supervisor = self
            .test
            .get_overrides()
            .spawn_supervisor(&chains.config, &chains.registry);

        let _drop_handles = chains
            .chain_handles
            .iter()
            .map(|handle| DropChainHandle(handle.clone()))
            .collect::<Vec<_>>();

        self.test.run(config, chains)?;

        Ok(())
    }
}

impl<'a, Test, const SIZE: usize> RunOwnedNaryChainTest<'a, Test, SIZE>
where
    Test: OwnedNaryChainTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunOwnedNaryChainTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
