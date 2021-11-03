use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use tracing::info;

use super::node::{run_owned_binary_node_test, OwnedBinaryNodeTest};
use crate::bootstrap::binary::chain::boostrap_chain_pair_with_nodes;
use crate::config::TestConfig;
use crate::error::Error;
use crate::relayer::supervisor::SupervisorHandle;
use crate::types::binary::chains::ConnectedChains;
use crate::types::single::node::RunningNode;

pub fn run_binary_chain_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_chain_test(&RunBinaryChainTest { test }, overrides)
}

pub fn run_two_way_binary_chain_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_chain_test(&RunTwoWayBinaryChainTest { test }, overrides)
}

pub fn run_owned_binary_chain_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: OwnedBinaryChainTest,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_node_test(RunOwnedBinaryChainTest { test, overrides })
}

pub trait RelayerConfigOverride {
    fn modify_relayer_config(&self, config: &mut Config);
}

pub trait SupervisorOverride {
    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle + 'static>,
    ) -> Option<SupervisorHandle>;
}

pub trait BinaryChainTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        deployment: &ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChainTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        deployment: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub struct RunOwnedBinaryChainTest<'a, Test, Overrides> {
    pub test: &'a Test,
    pub overrides: &'a Overrides,
}

pub struct RunBinaryChainTest<'a, Test> {
    pub test: &'a Test,
}

pub struct RunTwoWayBinaryChainTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test, Overrides> OwnedBinaryNodeTest for RunOwnedBinaryChainTest<'a, Test, Overrides>
where
    Test: OwnedBinaryChainTest,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    fn run(
        &self,
        config: &TestConfig,
        node_a: RunningNode,
        node_b: RunningNode,
    ) -> Result<(), Error> {
        let chains = boostrap_chain_pair_with_nodes(&config, node_a, node_b, |config| {
            self.overrides.modify_relayer_config(config);
        })?;

        let _supervisor = self
            .overrides
            .spawn_supervisor(&chains.config, &chains.registry);

        self.test.run(config, chains)?;

        // No use hanging the test on owned failures, as the chains
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<'a, Test: BinaryChainTest> OwnedBinaryChainTest for RunBinaryChainTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running one-way chain test, from {} to {}",
            chains.side_a.chain_id(),
            chains.side_b.chain_id()
        );

        self.test
            .run(config, &chains)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test: BinaryChainTest> OwnedBinaryChainTest for RunTwoWayBinaryChainTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running two-way chain test, from {} to {}",
            chains.side_a.chain_id(),
            chains.side_b.chain_id()
        );

        self.test
            .run(config, &chains)
            .map_err(config.hang_on_error())?;

        info!(
            "running two-way chain test in the opposite direction, from {} to {}",
            chains.side_b.chain_id(),
            chains.side_a.chain_id()
        );

        let chains = chains.flip();

        self.test
            .run(config, &chains)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}
