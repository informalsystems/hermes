/*!
   Constructs for running test cases with two chains,
   together with the relayer setup with chain handles and foreign clients.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use tracing::info;

use crate::bootstrap::binary::chain::boostrap_chain_pair_with_nodes;
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::node::{
    run_binary_node_test, run_single_node_test, BinaryNodeTest, NodeConfigOverride,
};
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::{ConnectedChains, DropChainHandle};
use crate::types::config::TestConfig;
use crate::types::env::write_env;
use crate::types::single::node::FullNode;

/**
   Runs a test case that implements [`BinaryChainTest`], with
   the test case being executed twice, with the second time having the
   position of the two chains flipped.
*/
pub fn run_two_way_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + TestConfigOverride,
{
    run_binary_chain_test(&RunTwoWayBinaryChainTest::new(test))
}

/**
   Runs a test case that implements [`BinaryChainTest`].
*/
pub fn run_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + TestConfigOverride,
{
    run_binary_node_test(&RunBinaryChainTest::new(test))
}

/**
   Runs a test case that implements [`BinaryChainTest`], with
   the test case being executed with a single chain that is connected
   to itself.
*/
pub fn run_self_connected_binary_chain_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + TestConfigOverride,
{
    run_single_node_test(&RunBinaryChainTest::new(test))
}

/**
   This trait is implemented for test cases that need to have two
   full nodes running together with the relayer setup with chain
   handles and foreign clients.

   Test writers can use this to implement test cases that only
   need the chains and relayers setup without the connection or
   channel handshake.
*/
pub trait BinaryChainTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override the
   relayer config before the relayer gets initialized.

   This is called by [`RunBinaryChainTest`] before after the
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
   A wrapper type that lifts a test case that implements [`BinaryChainTest`]
   into a test case the implements [`BinaryNodeTest`].
*/
pub struct RunBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChainTest`]
   into a test case the implements [`BinaryChainTest`].

   During execution, the underlying [`BinaryChainTest`] is run twice, with
   the second time having the position of the two chains flipped.
*/
pub struct RunTwoWayBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChainTest`]
   into a test case that implements [`BinaryNodeTest`].

   During execution, the test case is given a [`ConnectedChains`] with a
   single underlying chain that is connected to itself.
*/
pub struct RunSelfConnectedBinaryChainTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
{
    /// Create a new [`RunBinaryChainTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunTwoWayBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
{
    /// Create a new [`RunTwoWayBinaryChainTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunSelfConnectedBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
{
    /// Create a new [`RunSelfConnectedBinaryChainTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> BinaryNodeTest for RunBinaryChainTest<'a, Test>
where
    Test: BinaryChainTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride,
{
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error> {
        let (relayer, chains) = boostrap_chain_pair_with_nodes(config, node_a, node_b, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let env_path = config.chain_store_dir.join("binary-chains.env");

        write_env(&env_path, &(&relayer, &chains))?;

        info!("written chains environment to {}", env_path.display());

        let _drop_handle_a = DropChainHandle(chains.handle_a.clone());
        let _drop_handle_b = DropChainHandle(chains.handle_b.clone());

        self.test
            .run(config, relayer, chains)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test: BinaryChainTest> BinaryChainTest for RunTwoWayBinaryChainTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running two-way chain test, from {} to {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
        );

        self.test.run(config, relayer.clone(), chains.clone())?;

        info!(
            "running two-way chain test in the opposite direction, from {} to {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
        );

        let chains = chains.flip();

        self.test.run(config, relayer, chains)?;

        Ok(())
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
