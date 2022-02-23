/*!
   Constructs for running test cases with two full nodes together with the
   relayer setup with chain handles and foreign clients, as well as
   connected IBC channels with completed handshakes.
*/

use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use super::chain::{
    run_binary_chain_test, BinaryChainTest, RelayerConfigOverride, SupervisorOverride,
};
use super::node::NodeConfigOverride;
use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::config::TestConfig;
use crate::types::env::write_env;

/**
   Runs a test case that implements [`BinaryChannelTest`], with
   the test case being executed twice, with the second time having the position
   of the two chains flipped.
*/
pub fn run_two_way_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride
        + RelayerConfigOverride
        + SupervisorOverride
        + PortsOverride
        + ChannelOrderOverride
        + TestConfigOverride,
{
    run_binary_channel_test(&RunTwoWayBinaryChannelTest::new(test))
}

/**
   Runs a test case that implements [`BinaryChannelTest`].
*/
pub fn run_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride
        + RelayerConfigOverride
        + SupervisorOverride
        + PortsOverride
        + ChannelOrderOverride
        + TestConfigOverride,
{
    run_binary_chain_test(&RunBinaryChannelTest::new(test))
}

/**
   An owned version of [`BinaryChannelTest`], which the test case is given
   owned [`ConnectedChains`] and [`ConnectedChannel`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   and relayer will be stopped at the end of the test case.
   The test framework cannot use functions such as
   [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
*/
pub trait BinaryChannelTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override
   the port IDs used when creating the channels.

   This is called by [`RunBinaryChannelTest`] before creating
   the IBC channels.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait PortsOverride {
    /**
       Return the port ID for chain A.
    */
    fn channel_port_a(&self) -> PortId;

    /**
       Return the port ID for chain B.
    */
    fn channel_port_b(&self) -> PortId;
}

pub trait ChannelOrderOverride {
    fn channel_order(&self) -> Order;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
   into a test case the implements [`BinaryChainTest`].
*/
pub struct RunBinaryChannelTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
   into a test case the implements [`BinaryChannelTest`].
*/
pub struct RunTwoWayBinaryChannelTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunBinaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
{
    /// Create a new [`RunBinaryChannelTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunTwoWayBinaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
{
    /// Create a new [`BinaryChannelTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> BinaryChainTest for RunBinaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: PortsOverride + ChannelOrderOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let overrides = self.test.get_overrides();

        let port_a = overrides.channel_port_a();
        let port_b = overrides.channel_port_b();
        let order = overrides.channel_order();

        let channels = bootstrap_channel_with_chains(
            &chains,
            &port_a,
            &port_b,
            order,
            config.bootstrap_with_random_ids,
        )?;

        let env_path = config.chain_store_dir.join("binary-channels.env");

        write_env(&env_path, &(&chains, &channels))?;

        info!("written channel environment to {}", env_path.display());

        self.test
            .run(config, chains, channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test: BinaryChannelTest> BinaryChannelTest for RunTwoWayBinaryChannelTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running two-way channel test, from {}/{} to {}/{}",
            chains.chain_id_a(),
            channels.channel_id_a,
            chains.chain_id_b(),
            channels.channel_id_b,
        );

        self.test
            .run(config, chains.clone(), channels.clone())
            .map_err(config.hang_on_error())?;

        info!(
            "running two-way channel test in the opposite direction, from {}/{} to {}/{}",
            chains.chain_id_b(),
            channels.channel_id_b,
            chains.chain_id_a(),
            channels.channel_id_a,
        );

        let chains = chains.flip();
        let channels = channels.flip();

        self.test
            .run(config, chains, channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test, Overrides> HasOverrides for RunBinaryChannelTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunTwoWayBinaryChannelTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
