use ibc_relayer::config::Config;

use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::init::init_test;

pub trait TestCase {
    fn run(&self) -> Result<(), Error>;
}

pub fn run_test(test: impl TestCase) -> Result<(), Error> {
    test.run()
}

pub trait BasicTestCase {
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

struct RunBasicTestCase<Test>(Test);

impl<Test: BasicTestCase> TestCase for RunBasicTestCase<Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);
        BasicTestCase::run(&self.0, &config, &builder)
    }
}

pub fn run_basic_test(test: impl BasicTestCase) -> Result<(), Error> {
    run_test(RunBasicTestCase(test))
}

pub trait ConfigurableTestCase {
    fn modify_relayer_config(&self, _config: &mut Config) {}
}

pub struct NoTestConfig<Test>(pub Test);

impl<Test> ConfigurableTestCase for NoTestConfig<Test> {}
