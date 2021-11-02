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

pub fn run_basic_test(test: impl BasicTest) -> Result<(), Error> {
    run_test(RunBasicTest(test))
}

pub trait TestCase {
    fn run(&self) -> Result<(), Error>;
}

pub trait BasicTest {
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

pub trait TestWithRelayerConfigOverride {
    fn modify_relayer_config(&self, _config: &mut Config) {}
}

struct RunBasicTest<Test>(Test);

impl<Test: BasicTest> TestCase for RunBasicTest<Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);
        BasicTest::run(&self.0, &config, &builder)
    }
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
