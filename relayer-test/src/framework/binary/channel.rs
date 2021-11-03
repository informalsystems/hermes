use core::str::FromStr;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use super::chain::{
    run_owned_binary_chain_test, OwnedBinaryChainTest, TestWithRelayerConfigOverride,
};
use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::config::TestConfig;
use crate::error::Error;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::Channel;

pub fn run_binary_channel_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Overrides: TestWithRelayerConfigOverride + TestWithChannelPortsOverride,
{
    run_owned_binary_channel_test(&RunBinaryChannelTest { test }, overrides)
}

pub fn run_two_way_binary_channel_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: BinaryChannelTest,
    Overrides: TestWithRelayerConfigOverride + TestWithChannelPortsOverride,
{
    run_owned_binary_channel_test(&RunTwoWayBinaryChannelTest { test }, overrides)
}

pub fn run_owned_binary_channel_test<Test, Overrides>(
    test: &Test,
    overrides: &Overrides,
) -> Result<(), Error>
where
    Test: OwnedBinaryChannelTest,
    Overrides: TestWithRelayerConfigOverride + TestWithChannelPortsOverride,
{
    run_owned_binary_chain_test(&RunOwnedBinaryChannelTest { test, overrides }, overrides)
}

pub trait BinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait TestWithChannelPortsOverride {
    fn channel_port_a(&self) -> String {
        "transfer".to_string()
    }

    fn channel_port_b(&self) -> String {
        "transfer".to_string()
    }
}

pub struct RunOwnedBinaryChannelTest<'a, Test, Overrides> {
    pub test: &'a Test,
    pub overrides: &'a Overrides,
}

pub struct RunBinaryChannelTest<'a, Test> {
    pub test: &'a Test,
}

pub struct RunTwoWayBinaryChannelTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test, Overrides> OwnedBinaryChainTest for RunOwnedBinaryChannelTest<'a, Test, Overrides>
where
    Test: OwnedBinaryChannelTest,
    Overrides: TestWithChannelPortsOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = PortId::from_str(&self.overrides.channel_port_a())?;
        let port_b = PortId::from_str(&self.overrides.channel_port_b())?;

        let channels = bootstrap_channel_with_chains(&chains, &port_a, &port_b)?;

        self.test.run(config, chains, channels)?;

        // No use hanging the test on owned failures, as the chains and channels
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
