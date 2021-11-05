/*!
   Constructs for running test cases with two full nodes together with the
   relayer setup with chain handles and foreign clients, as well as
   connected IBC channels with completed handshakes.
*/

use core::str::FromStr;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use super::chain::{
    run_owned_binary_chain_test, OwnedBinaryChainTest, RelayerConfigOverride, SupervisorOverride,
};
use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::Channel;
use crate::types::config::TestConfig;

/**
   Runs a test case that implements [`BinaryChannelTest`].
*/
pub fn run_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride + PortsOverride,
{
    run_owned_binary_channel_test(&RunBinaryChannelTest { test })
}

/**
   Runs a test case that implements [`BinaryChannelTest`], with
   the test case being executed twice, with the second time having the position
   of the two chains flipped.
*/
pub fn run_two_way_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride + PortsOverride,
{
    run_owned_binary_channel_test(&RunTwoWayBinaryChannelTest { test })
}

/**
   Runs a test case that implements [`OwnedBinaryChannelTest`].
*/
pub fn run_owned_binary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: OwnedBinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride + SupervisorOverride + PortsOverride,
{
    run_owned_binary_chain_test(&RunOwnedBinaryChannelTest { test })
}

/**
   This trait is implemented for test cases that need to have two
   full nodes running together with the relayer setup with chain
   handles and foreign clients, together with connected IBC channels
   with completed handshakes.

   The test case is given a reference to [`ConnectedChains`],
   and a reference to [`Channel`].

   Test writers can use this to implement test cases that only
   need the chains and relayers setup without the channel handshake.
*/
pub trait BinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An owned version of [`BinaryChannelTest`], which the test case is given
   owned [`ConnectedChains`] and [`Channel`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   and relayer will be stopped at the end of the test case.
   The test framework cannot use functions such as
   [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
*/
pub trait OwnedBinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override
   the port IDs used when creating the channels.

   This is called by [`RunOwnedBinaryChannelTest`] before creating
   the IBC channels.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait PortsOverride {
    /**
       Return the port ID for chain A.
    */
    fn channel_port_a(&self) -> String;

    /**
       Return the port ID for chain B.
    */
    fn channel_port_b(&self) -> String;
}

/**
   A wrapper type that lifts a test case that implements [`OwnedBinaryChannelTest`]
   into a test case the implements [`OwnedBinaryChainTest`].
*/
pub struct RunOwnedBinaryChannelTest<'a, Test> {
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
   into a test case the implements [`OwnedBinaryChannelTest`]. During execution,
   the underlying [`BinaryChannelTest`] is run twice, with the second time
   having the position of the two chains flipped.
*/
pub struct RunBinaryChannelTest<'a, Test> {
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
   into a test case the implements [`OwnedBinaryChannelTest`].
*/
pub struct RunTwoWayBinaryChannelTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test, Overrides> OwnedBinaryChainTest for RunOwnedBinaryChannelTest<'a, Test>
where
    Test: OwnedBinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: PortsOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = PortId::from_str(&self.test.get_overrides().channel_port_a())?;
        let port_b = PortId::from_str(&self.test.get_overrides().channel_port_b())?;

        let channels = bootstrap_channel_with_chains(&chains, &port_a, &port_b)?;

        self.test.run(config, chains, channels)?;

        // No use suspending the test on owned failures, as the chains and channels
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<'a, Test: BinaryChannelTest> OwnedBinaryChannelTest for RunBinaryChannelTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test
            .run(config, &chains, &channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test: BinaryChannelTest> OwnedBinaryChannelTest for RunTwoWayBinaryChannelTest<'a, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running two-way channel test, from {}/{} to {}/{}",
            chains.side_a.chain_id(),
            channels.channel_id_a,
            chains.side_b.chain_id(),
            channels.channel_id_b,
        );

        self.test
            .run(config, &chains, &channels)
            .map_err(config.hang_on_error())?;

        info!(
            "running two-way channel test in the opposite direction, from {}/{} to {}/{}",
            chains.side_b.chain_id(),
            channels.channel_id_b,
            chains.side_a.chain_id(),
            channels.channel_id_a,
        );

        let chains = chains.flip();
        let channels = channels.flip();

        self.test
            .run(config, &chains, &channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<'a, Test, Overrides> HasOverrides for RunOwnedBinaryChannelTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
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
