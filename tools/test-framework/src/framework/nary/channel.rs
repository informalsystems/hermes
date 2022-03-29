/*!
   Constructs for running test cases with more than two chains,
   together with the relayer setup with chain handles and foreign clients,
   as well as connected IBC channels with completed handshakes.
*/

use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::nary::channel::bootstrap_channels_with_connections;
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::chain::RelayerConfigOverride;
use crate::framework::binary::channel::{BinaryChannelTest, ChannelOrderOverride};
use crate::framework::binary::connection::ConnectionDelayOverride;
use crate::framework::binary::node::{NodeConfigOverride, NodeGenesisOverride};
use crate::framework::nary::chain::RunNaryChainTest;
use crate::framework::nary::connection::{NaryConnectionTest, RunNaryConnectionTest};
use crate::framework::nary::node::run_nary_node_test;
use crate::framework::supervisor::{RunWithSupervisor, SupervisorOverride};
use crate::relayer::driver::RelayerDriver;
use crate::types::config::TestConfig;
use crate::types::nary::chains::NaryConnectedChains;
use crate::types::nary::channel::ConnectedChannels;
use crate::types::nary::connection::ConnectedConnections;
use crate::util::suspend::hang_on_error;

pub fn run_nary_channel_test<Test, Overrides, const SIZE: usize>(test: &Test) -> Result<(), Error>
where
    Test: NaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + SupervisorOverride
        + ConnectionDelayOverride
        + PortsOverride<SIZE>
        + ChannelOrderOverride,
{
    run_nary_node_test(&RunNaryChainTest::new(&RunNaryConnectionTest::new(
        &RunNaryChannelTest::new(&RunWithSupervisor::new(test)),
    )))
}

pub fn run_binary_as_nary_channel_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + SupervisorOverride
        + ConnectionDelayOverride
        + PortsOverride<2>
        + ChannelOrderOverride,
{
    run_nary_channel_test(&RunBinaryAsNaryChannelTest::new(test))
}

/**
   Returns a `SIZE`x`SIZE` number of transfer ports.

   This can be used by N-ary channel test cases to have a default
   implementation of `PortsOverride`, with `"transfer"` used for
   all port IDs.
*/
pub fn transfer_port_overrides<const SIZE: usize>() -> [[PortId; SIZE]; SIZE] {
    let port = PortId::transfer();
    let ports_ref = [[&port; SIZE]; SIZE];
    ports_ref.map(|inner_ports| inner_ports.map(Clone::clone))
}

/**
    This trait is implemented for test cases that need to have more than
    two chains running with connected channels.
*/
pub trait NaryChannelTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, SIZE>,
        channels: ConnectedChannels<Handle, SIZE>,
    ) -> Result<(), Error>;
}

/**
    An internal trait that can be implemented by test cases to override
    the port IDs used when creating N-ary channels.

    When called, the implementer returns a `SIZE`x`SIZE` matrix
    of [`PortId`]s to indicate which port ID for the chain at
    the first position when connected to the chain at the second
    position.

    This is called by [`RunNaryChannelTest`] before creating
    the IBC channels.

    Note that this trait is not automatically implemented
    for test cases via
    [`TestOverrides`](crate::framework::overrides::TestOverrides),
    except for the binary case `PortsOverride<2>`.
    So each N-ary channel test must also implement this trait manually.

    It is possible to implement this with an empty body, in which case
    the port ID matrix will all be populated with `"transfer"` ports.
*/
pub trait PortsOverride<const SIZE: usize> {
    fn channel_ports(&self) -> [[PortId; SIZE]; SIZE] {
        transfer_port_overrides()
    }
}

/**
    A wrapper type that lifts a test case that implements [`NaryChannelTest`]
    into a test case the implements [`NaryConnectionTest`].
*/
pub struct RunNaryChannelTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

/**
    A wrapper type that lifts a test case that implements [`BinaryChannelTest`]
    into a test case the implements [`NaryChannelTest`].

    This can be used to test the implementation of the N-ary test framework,
    by running binary channel tests as N-ary channel tests.
*/
pub struct RunBinaryAsNaryChannelTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, const SIZE: usize> RunNaryChannelTest<'a, Test, SIZE>
where
    Test: NaryChannelTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunBinaryAsNaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides, const SIZE: usize> NaryConnectionTest<SIZE>
    for RunNaryChannelTest<'a, Test, SIZE>
where
    Test: NaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: PortsOverride<SIZE> + ChannelOrderOverride,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, SIZE>,
        connections: ConnectedConnections<Handle, SIZE>,
    ) -> Result<(), Error> {
        let overrides = self.test.get_overrides();
        let port_ids = overrides.channel_ports();
        let order = overrides.channel_order();

        let channels = bootstrap_channels_with_connections(
            connections,
            chains.chain_handles().clone(),
            port_ids,
            order,
            config.bootstrap_with_random_ids,
        )?;

        self.test.run(config, relayer, chains, channels)?;

        Ok(())
    }
}

impl<'a, Test> NaryChannelTest<2> for RunBinaryAsNaryChannelTest<'a, Test>
where
    Test: BinaryChannelTest,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 2>,
        channels: ConnectedChannels<Handle, 2>,
    ) -> Result<(), Error> {
        self.test
            .run(config, relayer, chains.into(), channels.into())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> NaryChannelTest<SIZE> for RunWithSupervisor<'a, Test>
where
    Test: NaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: SupervisorOverride,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, SIZE>,
        channels: ConnectedChannels<Handle, SIZE>,
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

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunNaryChannelTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunBinaryAsNaryChannelTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
