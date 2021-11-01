use core::str::FromStr;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;

use crate::bootstrap::deployment::ChainDeployment;
use crate::error::Error;
use crate::relayer::channel::{bootstrap_channel, Channel};
use crate::tagged::*;

use super::super::base::{ConfigurableTestCase, NoTestConfig};
use super::chain::{run_owned_binary_chain_test, OwnedBinaryChainTestCase};

pub fn run_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTestCase + ConfigurableTestCase + TestCaseWithChannelPorts,
{
    run_owned_binary_channel_test(RunBinaryChannelTest(test))
}

pub fn run_two_way_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChannelTestCase + ConfigurableTestCase + TestCaseWithChannelPorts,
{
    run_owned_binary_channel_test(RunTwoWayBinaryChannelTest(test))
}

pub fn run_owned_binary_channel_test<Test>(test: Test) -> Result<(), Error>
where
    Test: OwnedBinaryChannelTestCase + TestCaseWithChannelPorts + ConfigurableTestCase,
{
    run_owned_binary_chain_test(RunOwnedBinaryChannelTest(test))
}

pub trait BinaryChannelTestCase {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: &ChainDeployment<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChannelTestCase {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait TestCaseWithChannelPorts {
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

impl<Test> TestCaseWithChannelPorts for NoTestConfig<Test> {}

impl<Test: OwnedBinaryChannelTestCase> OwnedBinaryChannelTestCase for NoTestConfig<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(chains, channels)
    }
}

impl<Test> OwnedBinaryChainTestCase for RunOwnedBinaryChannelTest<Test>
where
    Test: OwnedBinaryChannelTestCase + TestCaseWithChannelPorts,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = DualTagged::new(PortId::from_str(&self.0.channel_port_a())?);
        let port_b = DualTagged::new(PortId::from_str(&self.0.channel_port_b())?);

        let channels = bootstrap_channel(
            &chains.client_b_to_a,
            &chains.client_a_to_b,
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        self.0.run(chains, channels)?;

        Ok(())
    }
}

impl<Test: ConfigurableTestCase> ConfigurableTestCase for RunOwnedBinaryChannelTest<Test> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Test: BinaryChannelTestCase> BinaryChannelTestCase for NoTestConfig<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: &ChainDeployment<ChainA, ChainB>,
        channels: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(chains, channels)
    }
}

impl<Test: BinaryChannelTestCase> OwnedBinaryChannelTestCase for RunBinaryChannelTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        chains: ChainDeployment<ChainA, ChainB>,
        channels: Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(&chains, &channels)
    }
}

impl<Test: TestCaseWithChannelPorts> TestCaseWithChannelPorts for RunBinaryChannelTest<Test> {
    fn channel_port_a(&self) -> String {
        self.0.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.0.channel_port_b()
    }
}

impl<Test: ConfigurableTestCase> ConfigurableTestCase for RunBinaryChannelTest<Test> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Test: BinaryChannelTestCase> OwnedBinaryChannelTestCase for RunTwoWayBinaryChannelTest<Test> {
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

impl<Test: TestCaseWithChannelPorts> TestCaseWithChannelPorts for RunTwoWayBinaryChannelTest<Test> {
    fn channel_port_a(&self) -> String {
        self.0.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.0.channel_port_b()
    }
}

impl<Test: ConfigurableTestCase> ConfigurableTestCase for RunTwoWayBinaryChannelTest<Test> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}
