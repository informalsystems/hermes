use core::str::FromStr;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use tracing::info;

use super::chain::{
    run_owned_binary_chain_test, OwnedBinaryChainTest, TestWithRelayerConfigOverride,
};
use crate::bootstrap::binary::channel::bootstrap_channel_with_chains;
use crate::config::TestConfig;
use crate::error::Error;
use crate::framework::overrides::{
    HasOverrideChannelPorts, OnlyOverrideRelayerConfig, OverrideNone, TestWithOverrides,
};
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::Channel;

pub fn run_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTest + TestWithRelayerConfigOverride + TestWithChannelPortsOverride,
{
    run_owned_binary_channel_test(RunBinaryChannelTest(test))
}

pub fn run_two_way_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTest + TestWithRelayerConfigOverride + TestWithChannelPortsOverride,
{
    run_owned_binary_channel_test(RunTwoWayBinaryChannelTest(test))
}

pub fn run_owned_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: OwnedBinaryChannelTest + TestWithChannelPortsOverride + TestWithRelayerConfigOverride,
{
    run_owned_binary_chain_test(RunOwnedBinaryChannelTest(test))
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

struct RunOwnedBinaryChannelTest<Test>(Test);

struct RunBinaryChannelTest<Test>(Test);

struct RunTwoWayBinaryChannelTest<Test>(Test);

impl<Test> OwnedBinaryChainTest for RunOwnedBinaryChannelTest<Test>
where
    Test: OwnedBinaryChannelTest + TestWithChannelPortsOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = PortId::from_str(&self.0.channel_port_a())?;
        let port_b = PortId::from_str(&self.0.channel_port_b())?;

        let channels = bootstrap_channel_with_chains(&chains, &port_a, &port_b)?;

        self.0.run(config, chains, channels)?;

        // No use hanging the test on owned failures, as the chains and channels
        // are dropped in the inner test already.

        Ok(())
    }
}

impl<Test: BinaryChannelTest> OwnedBinaryChannelTest for RunBinaryChannelTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0
            .run(config, &chains, &channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<Test: BinaryChannelTest> OwnedBinaryChannelTest for RunTwoWayBinaryChannelTest<Test> {
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

        self.0
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

        self.0
            .run(config, &chains, &channels)
            .map_err(config.hang_on_error())?;

        Ok(())
    }
}

impl<Test> TestWithChannelPortsOverride for TestWithOverrides<OverrideNone, Test> {}

impl<Test> TestWithChannelPortsOverride for TestWithOverrides<OnlyOverrideRelayerConfig, Test> {}

impl<Override, Test: OwnedBinaryChannelTest> OwnedBinaryChannelTest
    for TestWithOverrides<Override, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(config, chains, channels)
    }
}

impl<Override, Test: BinaryChannelTest> BinaryChannelTest for TestWithOverrides<Override, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        chains: &ConnectedChains<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(config, chains, channels)
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunOwnedBinaryChannelTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Override, Test> TestWithChannelPortsOverride for TestWithOverrides<Override, Test>
where
    Override: HasOverrideChannelPorts,
    Test: TestWithChannelPortsOverride,
{
    fn channel_port_a(&self) -> String {
        self.test.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.test.channel_port_b()
    }
}

impl<Test: TestWithChannelPortsOverride> TestWithChannelPortsOverride
    for RunBinaryChannelTest<Test>
{
    fn channel_port_a(&self) -> String {
        self.0.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.0.channel_port_b()
    }
}

impl<Test: TestWithChannelPortsOverride> TestWithChannelPortsOverride
    for RunTwoWayBinaryChannelTest<Test>
{
    fn channel_port_a(&self) -> String {
        self.0.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.0.channel_port_b()
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunBinaryChannelTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunTwoWayBinaryChannelTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}
