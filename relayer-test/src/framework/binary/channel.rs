use core::str::FromStr;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;

use super::chain::{run_owned_binary_chain_test, OwnedBinaryChainTest};
use crate::bootstrap::channel::bootstrap_channel_with_chains;
use crate::error::Error;
use crate::framework::base::TestWithRelayerConfigOverride;
use crate::framework::overrides::{
    HasOverrideChannelPorts, OnlyOverrideRelayerConfig, OverrideNone, TestWithOverrides,
};
use crate::types::binary::chains::ChainDeployment;
use crate::types::binary::channel::Channel;

pub fn run_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTest + TestWithRelayerConfigOverride + TestWithChannelPorts,
{
    run_owned_binary_channel_test(RunBinaryChannelTest(test))
}

pub fn run_two_way_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTest + TestWithRelayerConfigOverride + TestWithChannelPorts,
{
    run_owned_binary_channel_test(RunTwoWayBinaryChannelTest(test))
}

pub fn run_owned_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: OwnedBinaryChannelTest + TestWithChannelPorts + TestWithRelayerConfigOverride,
{
    run_owned_binary_chain_test(RunOwnedBinaryChannelTest(test))
}

pub trait BinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: &ChainDeployment<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait TestWithChannelPorts {
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

impl<Override, Test> TestWithChannelPorts for TestWithOverrides<Override, Test>
where
    Override: HasOverrideChannelPorts,
    Test: TestWithChannelPorts,
{
    fn channel_port_a(&self) -> String {
        self.test.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.test.channel_port_b()
    }
}

impl<Test> TestWithChannelPorts for TestWithOverrides<OverrideNone, Test> {}

impl<Test> TestWithChannelPorts for TestWithOverrides<OnlyOverrideRelayerConfig, Test> {}

impl<Override, Test: OwnedBinaryChannelTest> OwnedBinaryChannelTest
    for TestWithOverrides<Override, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(chains, channels)
    }
}

impl<Test> OwnedBinaryChainTest for RunOwnedBinaryChannelTest<Test>
where
    Test: OwnedBinaryChannelTest + TestWithChannelPorts,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = PortId::from_str(&self.0.channel_port_a())?;
        let port_b = PortId::from_str(&self.0.channel_port_b())?;

        let channels = bootstrap_channel_with_chains(&chains, &port_a, &port_b)?;

        self.0.run(chains, channels)?;

        Ok(())
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunOwnedBinaryChannelTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Override, Test: BinaryChannelTest> BinaryChannelTest for TestWithOverrides<Override, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: &ChainDeployment<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(chains, channels)
    }
}

impl<Test: BinaryChannelTest> OwnedBinaryChannelTest for RunBinaryChannelTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(&chains, &channels)
    }
}

impl<Test: TestWithChannelPorts> TestWithChannelPorts for RunBinaryChannelTest<Test> {
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

impl<Test: BinaryChannelTest> OwnedBinaryChannelTest for RunTwoWayBinaryChannelTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(&chains, &channels)?;

        let chains = chains.flip();
        let channels = channels.flip();

        self.0.run(&chains, &channels)?;

        Ok(())
    }
}

impl<Test: TestWithChannelPorts> TestWithChannelPorts for RunTwoWayBinaryChannelTest<Test> {
    fn channel_port_a(&self) -> String {
        self.0.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.0.channel_port_b()
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunTwoWayBinaryChannelTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}
