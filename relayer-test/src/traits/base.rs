use ibc_relayer::config::Config;

use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::init::init_test;

use super::overrides::{
    HasOverrideRelayerConfig, OnlyOverrideChannelPorts, OverrideNone, TestWithOverrides,
};

pub fn run_test(test: impl TestCase) -> Result<(), Error> {
    test.run()
}

pub fn run_basic_test(test: impl BasicTestCase) -> Result<(), Error> {
    run_test(RunBasicTestCase(test))
}

pub trait TestCase {
    fn run(&self) -> Result<(), Error>;
}

pub trait BasicTestCase {
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

pub trait ConfigurableTestCase {
    fn modify_relayer_config(&self, _config: &mut Config) {}
}

struct RunBasicTestCase<Test>(Test);

impl<Test: BasicTestCase> TestCase for RunBasicTestCase<Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);
        BasicTestCase::run(&self.0, &config, &builder)
    }
}

impl<Override, Test> ConfigurableTestCase for TestWithOverrides<Override, Test>
where
    Test: ConfigurableTestCase,
    Override: HasOverrideRelayerConfig,
{
    fn modify_relayer_config(&self, config: &mut Config) {
        self.test.modify_relayer_config(config)
    }
}

impl<Test> ConfigurableTestCase for TestWithOverrides<OverrideNone, Test> {}

impl<Test> ConfigurableTestCase for TestWithOverrides<OnlyOverrideChannelPorts, Test> {}
