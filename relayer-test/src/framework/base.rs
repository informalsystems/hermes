use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::init::init_test;

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

struct RunBasicTest<Test>(Test);

impl<Test: BasicTest> TestCase for RunBasicTest<Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);
        BasicTest::run(&self.0, &config, &builder)
    }
}
