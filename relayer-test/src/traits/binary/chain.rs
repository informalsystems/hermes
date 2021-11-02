use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;

use crate::bootstrap::deployment::ChainDeployment;
use crate::bootstrap::pair::boostrap_chain_pair;
use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;

use super::super::base::{run_basic_test, BasicTestCase, ConfigurableTestCase};
use super::super::overrides::TestWithOverrides;

pub fn run_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChainTestCase + ConfigurableTestCase,
{
    run_owned_binary_chain_test(RunBinaryChainTest(test))
}

pub fn run_two_way_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: BinaryChainTestCase + ConfigurableTestCase,
{
    run_owned_binary_chain_test(RunTwoWayBinaryChainTest(test))
}

pub fn run_owned_binary_chain_test<Test>(test: Test) -> Result<(), Error>
where
    Test: OwnedBinaryChainTestCase + ConfigurableTestCase,
{
    run_basic_test(RunOwnedBinaryChainTest(test))
}

pub trait BinaryChainTestCase {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: &ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

pub trait OwnedBinaryChainTestCase {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

struct RunOwnedBinaryChainTest<Test>(Test);

struct RunBinaryChainTest<Test>(Test);

struct RunTwoWayBinaryChainTest<Test>(Test);

impl<Test> BasicTestCase for RunOwnedBinaryChainTest<Test>
where
    Test: OwnedBinaryChainTestCase + ConfigurableTestCase,
{
    fn run(&self, _config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let deployment = boostrap_chain_pair(&builder, |config| {
            self.0.modify_relayer_config(config);
        })?;

        self.0.run(deployment)?;

        Ok(())
    }
}

impl<Overrides, Test: OwnedBinaryChainTestCase> OwnedBinaryChainTestCase
    for TestWithOverrides<Overrides, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(deployment)
    }
}

impl<Overrides, Test: BinaryChainTestCase> BinaryChainTestCase
    for TestWithOverrides<Overrides, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: &ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.test.run(deployment)
    }
}

impl<Test: BinaryChainTestCase> OwnedBinaryChainTestCase for RunBinaryChainTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(&deployment)
    }
}

impl<Test: ConfigurableTestCase> ConfigurableTestCase for RunBinaryChainTest<Test> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}

impl<Test: BinaryChainTestCase> OwnedBinaryChainTestCase for RunTwoWayBinaryChainTest<Test> {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        deployment: ChainDeployment<ChainA, ChainB>,
    ) -> Result<(), Error> {
        self.0.run(&deployment)?;

        let deployment = deployment.flip();

        self.0.run(&deployment)?;

        Ok(())
    }
}

impl<Test: ConfigurableTestCase> ConfigurableTestCase for RunTwoWayBinaryChainTest<Test> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.0.modify_relayer_config(config);
    }
}
