use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::nary::channel::bootstrap_channels_with_connections;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::channel::BinaryChannelTest;
use crate::framework::binary::node::NodeConfigOverride;
use crate::framework::nary::connection::{run_nary_connection_test, NaryConnectionTest};
use crate::framework::overrides::TestOverrides;
use crate::relayer::driver::RelayerDriver;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::nary::channel::ConnectedChannels;
use crate::types::nary::connection::ConnectedConnections;

pub fn run_nary_channel_test<Test, Overrides, const SIZE: usize>(test: &Test) -> Result<(), Error>
where
    Test: NaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides:
        NodeConfigOverride + RelayerConfigOverride + SupervisorOverride + PortsOverride<SIZE>,
{
    run_nary_connection_test(&RunNaryChannelTest::new(test))
}

pub trait NaryChannelTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, SIZE>,
        channels: ConnectedChannels<Handle, SIZE>,
    ) -> Result<(), Error>;
}

pub trait PortsOverride<const SIZE: usize> {
    fn channel_ports(&self) -> [[PortId; SIZE]; SIZE];
}

pub struct RunNaryChannelTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

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
    Overrides: PortsOverride<SIZE>,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, SIZE>,
        connections: ConnectedConnections<Handle, SIZE>,
    ) -> Result<(), Error> {
        let port_ids = self.test.get_overrides().channel_ports();
        let channels =
            bootstrap_channels_with_connections(connections, &chains.chain_handles, port_ids)?;

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
        chains: ConnectedChains<Handle, 2>,
        channels: ConnectedChannels<Handle, 2>,
    ) -> Result<(), Error> {
        self.test
            .run(config, relayer, chains.into(), channels.into())
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

impl<Test: TestOverrides> PortsOverride<2> for Test {
    fn channel_ports(&self) -> [[PortId; 2]; 2] {
        let port_a = self.channel_port_a();
        let port_b = self.channel_port_b();

        [[port_a.clone(), port_b.clone()], [port_b, port_a]]
    }
}
