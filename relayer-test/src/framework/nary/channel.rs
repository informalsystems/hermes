use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::nary::channel::bootstrap_channels;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::channel::OwnedBinaryChannelTest;
use crate::framework::binary::node::NodeConfigOverride;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::nary::channel::ConnectedChannels;

use super::chain::{run_owned_nary_chain_test, OwnedNaryChainTest};

pub fn run_owned_nary_channel_test<Test, Overrides, const SIZE: usize>(
    test: &Test,
) -> Result<(), Error>
where
    Test: OwnedNaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides:
        NodeConfigOverride + RelayerConfigOverride + SupervisorOverride + PortsOverride<SIZE>,
{
    run_owned_nary_chain_test(&RunOwnedNaryChannelTest::new(test))
}

pub trait OwnedNaryChannelTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<Handle, SIZE>,
        channels: ConnectedChannels<Handle, SIZE>,
    ) -> Result<(), Error>;
}

pub trait PortsOverride<const SIZE: usize> {
    fn channel_ports(&self) -> [[PortId; SIZE]; SIZE];
}

pub struct RunOwnedNaryChannelTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

pub struct RunBinaryAsNaryChannelTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, const SIZE: usize> RunOwnedNaryChannelTest<'a, Test, SIZE>
where
    Test: OwnedNaryChannelTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunBinaryAsNaryChannelTest<'a, Test>
where
    Test: OwnedBinaryChannelTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides, const SIZE: usize> OwnedNaryChainTest<SIZE>
    for RunOwnedNaryChannelTest<'a, Test, SIZE>
where
    Test: OwnedNaryChannelTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: PortsOverride<SIZE>,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error> {
        let port_ids = self.test.get_overrides().channel_ports();
        let channels = bootstrap_channels(chains.foreign_clients.clone(), port_ids)?;

        self.test.run(config, chains, channels)?;

        Ok(())
    }
}

impl<'a, Test> OwnedNaryChannelTest<2> for RunBinaryAsNaryChannelTest<'a, Test>
where
    Test: OwnedBinaryChannelTest,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<Handle, 2>,
        channels: ConnectedChannels<Handle, 2>,
    ) -> Result<(), Error> {
        self.test.run(config, chains.into(), channels.into())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides
    for RunOwnedNaryChannelTest<'a, Test, SIZE>
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
