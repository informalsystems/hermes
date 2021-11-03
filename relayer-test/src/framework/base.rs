use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::init::init_test;

pub fn run_test<Test: TestCase>(test: &Test) -> Result<(), Error> {
    test.run()
}

pub fn run_basic_test<Test: BasicTest>(test: &Test) -> Result<(), Error> {
    run_test(&RunBasicTest { test })
}

pub trait TestCase {
    fn run(&self) -> Result<(), Error>;
}

pub trait BasicTest {
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

pub struct RunBasicTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test: BasicTest> TestCase for RunBasicTest<'a, Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);

        info!("starting test");

        self.test.run(&config, &builder)?;

        Ok(())
    }
}
