/*!
   Constructs for running test cases with two full nodes together with the
   relayer setup with chain handles and foreign clients, as well as
   connected IBC channels with completed handshakes.
*/

use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics04_channel::Version;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::bootstrap::binary::channel::{
    bootstrap_channel_with_connection, BootstrapChannelOptions,
};
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::chain::{
    ClientOptionsOverride, RelayerConfigOverride, RunBinaryChainTest,
};
use crate::framework::binary::connection::{
    BinaryConnectionTest, ConnectionDelayOverride, RunBinaryConnectionTest,
};
use crate::framework::binary::node::{
    run_binary_node_test, NodeConfigOverride, NodeGenesisOverride,
};
use crate::framework::supervisor::{RunWithSupervisor, SupervisorOverride};
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::config::TestConfig;
use crate::types::env::write_env;
use crate::types::tagged::*;
use crate::util::suspend::hang_on_error;

/**
   Runs a test case that implements [`BinaryChannelTest`], with
   the test case being executed twice, with the second time having the position
   of the two chains flipped.
*/
pub fn run_two_way_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + ClientOptionsOverride
        + SupervisorOverride
        + ConnectionDelayOverride
        + PortsOverride
        + ChannelOrderOverride
        + ChannelVersionOverride,
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
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + ClientOptionsOverride
        + SupervisorOverride
        + ConnectionDelayOverride
        + PortsOverride
        + ChannelOrderOverride
        + ChannelVersionOverride,
{
    run_binary_node_test(&RunBinaryChainTest::new(&RunBinaryConnectionTest::new(
        &RunBinaryChannelTest::new(&RunWithSupervisor::new(test)),
    )))
}

/**
   This trait is implemented for test cases that need to have two
   full nodes running together with the relayer setup with chain
   handles and foreign clients, together with connected IBC channels
   with completed handshakes.
*/
pub trait BinaryChannelTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
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

/**
   An internal trait for test cases to override the channel ordering
   when creating channels.

  This is called by [`RunBinaryChannelTest`] before creating
  the IBC channels.

  Test writers should implement
  [`TestOverrides`](crate::framework::overrides::TestOverrides)
  for their test cases instead of implementing this trait directly.
*/
pub trait ChannelOrderOverride {
    /**
       Return the channel ordering as [`Order`].
    */
    fn channel_order(&self) -> Order;
}

/** Facility for overriding the channel version */
pub trait ChannelVersionOverride {
    fn channel_version(&self) -> Version;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
   into a test case the implements [`BinaryConnectionTest`].
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

impl<'a, Test, Overrides> BinaryConnectionTest for RunBinaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: PortsOverride + ChannelOrderOverride + ChannelVersionOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let overrides = self.test.get_overrides();

        let port_a = overrides.channel_port_a();
        let port_b = overrides.channel_port_b();

        let bootstrap_options = BootstrapChannelOptions::default()
            .order(overrides.channel_order())
            .version(overrides.channel_version())
            .bootstrap_with_random_ids(config.bootstrap_with_random_ids);

        let channels = bootstrap_channel_with_connection(
            &chains.handle_a,
            &chains.handle_b,
            connection,
            &DualTagged::new(port_a).as_ref(),
            &DualTagged::new(port_b).as_ref(),
            bootstrap_options,
        )?;

        let env_path = config.chain_store_dir.join("binary-channels.env");

        write_env(&env_path, &(&chains, &(&relayer, &channels)))?;

        info!("written channel environment to {}", env_path.display());

        self.test.run(config, relayer, chains, channels)?;

        Ok(())
    }
}

impl<'a, Test: BinaryChannelTest> BinaryChannelTest for RunTwoWayBinaryChannelTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
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
            .run(config, relayer.clone(), chains.clone(), channels.clone())?;

        info!(
            "running two-way channel test in the opposite direction, from {}/{} to {}/{}",
            chains.chain_id_b(),
            channels.channel_id_b,
            chains.chain_id_a(),
            channels.channel_id_a,
        );

        let chains = chains.flip();
        let channels = channels.flip();

        self.test.run(config, relayer, chains, channels)?;

        Ok(())
    }
}

impl<'a, Test, Overrides> BinaryChannelTest for RunWithSupervisor<'a, Test>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: SupervisorOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        if self.get_overrides().should_spawn_supervisor() {
            relayer
                .clone()
                .with_supervisor(|| self.test.run(config, relayer, chains, channels))
        } else {
            hang_on_error(config.hang_on_fail, || {
                self.test.run(config, relayer, chains, channels)
            })
        }
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
