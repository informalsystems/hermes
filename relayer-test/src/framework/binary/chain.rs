/*!
   Constructs for running test cases with two full nodes
   together with the relayer setup with chain handles and foreign clients.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use tracing::info;

use super::node::{run_owned_binary_node_test, NodeConfigOverride, OwnedBinaryNodeTest};
use crate::bootstrap::binary::chain::boostrap_chain_pair_with_nodes;
use crate::bootstrap::binary::chain::boostrap_self_connected_chain;
use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::relayer::supervisor::SupervisorHandle;
use crate::types::binary::chains::ConnectedChains;
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;

/**
   Runs a test case that implements [`BinaryChainTest`].
*/
pub fn run_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_chain_test(&RunBinaryChainTest::new(test))
}

/**
   Runs a test case that implements [`BinaryChainTest`], with
   the test case being executed twice, with the second time having the
   position of the two chains flipped.
*/
pub fn run_two_way_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_chain_test(&RunTwoWayBinaryChainTest::new(test))
}

/**
   Runs a test case that implements [`OwnedBinaryChainTest`].
*/
pub fn run_owned_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: OwnedBinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_owned_binary_node_test(&RunOwnedBinaryChainTest::new(test))
}

/**
   Runs a test case that implements [`OwnedBinaryChainTest`], with
   the test case being executed with a single chain that is connected
   to itself.
*/
pub fn run_self_connected_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: OwnedBinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_basic_test(&RunSelfConnectedBinaryChainTest::new(test))
}

/**
   This trait is implemented for test cases that need to have two
   full nodes running together with the relayer setup with chain
   handles and foreign clients.

   The test case is given a reference to [`ConnectedChains`].

   Test writers can use this to implement test cases that only
   need the chains and relayers setup without the channel handshake.
*/
pub trait BinaryChainTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An owned version of [`BinaryChainTest`], which the test case is given
   owned [`ConnectedChains`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   and relayer will be stopped at the end of the test case.
   The test framework cannot use functions such as
   [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
*/
pub trait OwnedBinaryChainTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override the
   relayer config before the relayer gets initialized.

   This is called by [`RunOwnedBinaryChainTest`] before after the
   full nodes are running and before the relayer is initialized.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait RelayerConfigOverride {
    /// Modify the relayer config
    fn modify_relayer_config(&self, config: &mut Config);
}

/**
   An internal trait that can be implemented by test cases to disable
   the spawning of the relayer supervisor.

   This is called by [`RunOwnedBinaryChainTest`] after initializing
   the relayer to optionally spawn the relayer supervisor and
   return a supervisor handle.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait SupervisorOverride {
    /// Optionally spawn the supervisor
    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle + 'static>,
    ) -> Option<SupervisorHandle>;
}

/**
   A wrapper type that lifts a test case that implements [`OwnedBinaryChainTest`]
   into a test case the implements [`OwnedBinaryNodeTest`].
*/
pub struct RunOwnedBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChainTest`]
   into a test case the implements [`OwnedBinaryChainTest`].
*/
pub struct RunBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChainTest`]
   into a test case the implements [`OwnedBinaryChainTest`].

   During execution, the underlying [`BinaryChainTest`] is run twice, with
   the second time having the position of the two chains flipped.
*/
pub struct RunTwoWayBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`OwnedBinaryChainTest`]
   into a test case that implements [`BasicTest`].

   During execution, the test case is given a [`ConnectedChains`] with a
   single underlying chain that is connected to itself.
*/
pub struct RunSelfConnectedBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunOwnedBinaryChainTest<'a, Test>
where
    Test: OwnedBinaryChainTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunTwoWayBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunSelfConnectedBinaryChainTest<'a, Test>
where
    Test: OwnedBinaryChainTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> OwnedBinaryNodeTest for RunOwnedBinaryChainTest<'a, Test>
where
    Test: OwnedBinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride,
{
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error> {
        let chains = boostrap_chain_pair_with_nodes(config, node_a, node_b, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let _supervisor = self
            .test
            .get_overrides()
            .spawn_supervisor(&chains.config, &chains.registry);

        self.test.run(config, chains)?;

        // No use suspending the test on owned failures, as the chains
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
            chains.chain_id_a(),
            chains.chain_id_b(),
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
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        self.test
            .run(config, &chains)
            .map_err(config.hang_on_error())?;

        info!(
            "running two-way chain test in the opposite direction, from {} to {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
        );

        let chains = chains.flip();

        self.test
            .run(config, &chains)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test, Overrides> BasicTest for RunSelfConnectedBinaryChainTest<'a, Test>
where
    Test: OwnedBinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let node = bootstrap_single_node(builder, "refl", |config| {
            self.test.get_overrides().modify_node_config(config)
        })?;

        let chains = boostrap_self_connected_chain(config, node, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let _supervisor = self
            .test
            .get_overrides()
            .spawn_supervisor(&chains.config, &chains.registry);

        self.test.run(config, chains)?;

        // No use suspending the test on owned failures, as the chains
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<'a, Test, Overrides> HasOverrides for RunOwnedBinaryChainTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunBinaryChainTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunTwoWayBinaryChainTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunSelfConnectedBinaryChainTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
