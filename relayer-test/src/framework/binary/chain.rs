use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;

use crate::bootstrap::pair::boostrap_chain_pair;
use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::framework::base::{run_basic_test, BasicTest};
use crate::framework::overrides::{
    HasOverrideRelayerConfig, OnlyOverrideChannelPorts, OverrideNone, TestWithOverrides,
};
use crate::types::binary::chains::ConnectedChains;

pub fn run_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChainTest + TestWithRelayerConfigOverride,
{
    run_owned_binary_chain_test(RunBinaryChainTest(test))
}

pub fn run_two_way_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChainTest + TestWithRelayerConfigOverride,
{
    run_owned_binary_chain_test(RunTwoWayBinaryChainTest(test))
}

pub fn run_owned_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: OwnedBinaryChainTest + TestWithRelayerConfigOverride,
{
    run_basic_test(RunOwnedBinaryChainTest(test))
}

pub trait TestWithRelayerConfigOverride {
    fn modify_relayer_config(&self, _config: &mut Config) {}
}

pub trait BinaryChainTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: &ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChainTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

impl<Override, Test> TestWithRelayerConfigOverride for TestWithOverrides<Override, Test>
where
    Test: TestWithRelayerConfigOverride,
    Override: HasOverrideRelayerConfig,
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.test.modify_relayer_config(config)
    }
}

impl<Test> TestWithRelayerConfigOverride for TestWithOverrides<OverrideNone, Test> {}

impl<Test> TestWithRelayerConfigOverride for TestWithOverrides<OnlyOverrideChannelPorts, Test> {}

struct RunOwnedBinaryChainTest<Test>(Test);

struct RunBinaryChainTest<Test>(Test);

struct RunTwoWayBinaryChainTest<Test>(Test);

impl<Test> BasicTest for RunOwnedBinaryChainTest<Test>
where
    Test: OwnedBinaryChainTest + TestWithRelayerConfigOverride,
{
    fn run(&self, _config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let deployment = boostrap_chain_pair(&builder, |config| {
            self.0.modify_relayer_config(config);
        })?;

        self.0.run(deployment)?;

        Ok(())
    }
}

impl<Overrides, Test: OwnedBinaryChainTest> OwnedBinaryChainTest
    for TestWithOverrides<Overrides, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(deployment)
    }
}

impl<Overrides, Test: BinaryChainTest> BinaryChainTest for TestWithOverrides<Overrides, Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: &ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(deployment)
    }
}

impl<Test: BinaryChainTest> OwnedBinaryChainTest for RunBinaryChainTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let res = self.0.run(&deployment);

        deployment.supervisor_cmd_sender.stop();

        res
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunBinaryChainTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Test: BinaryChainTest> OwnedBinaryChainTest for RunTwoWayBinaryChainTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let res = self.0.run(&deployment);

        match res {
            Ok(()) => {
                let deployment = deployment.flip();

                let res = self.0.run(&deployment);
                deployment.supervisor_cmd_sender.stop();
                res
            }
            Err(e) => {
                deployment.supervisor_cmd_sender.stop();
                Err(e)
            }
        }
    }
}

impl<Test: TestWithRelayerConfigOverride> TestWithRelayerConfigOverride
    for RunTwoWayBinaryChainTest<Test>
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}
