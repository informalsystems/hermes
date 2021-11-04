/*!
    Base infrastructure for the test framework. Includes basic setup for
    initializing the logger and loading the test configuration.
*/

use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::config::TestConfig;
use crate::error::Error;
use crate::init::init_test;

/**
   Runs a primitive test case implementing [`PrimitiveTest`].
*/
pub fn run_test<Test: PrimitiveTest>(test: &Test) -> Result<(), Error> {
    test.run()
}

/**
   Runs a basic test case implementing [`BasicTest`].
*/
pub fn run_basic_test<Test: BasicTest>(test: &Test) -> Result<(), Error> {
    run_test(&RunBasicTest { test })
}

/**
   Used for test case wrappers to indicate that the inner test case
   implements override traits for overriding certain behavior of the test.

   Test writers do not need to be aware of this trait, as this is
   automatically handled by
   [TestOverrides](crate::framework::overrides::TestOverrides).
*/
pub trait HasOverrides {
    type Overrides;

    fn get_overrides(&self) -> &Self::Overrides;
}

/**
   A primitive test case provides no additional logic.
*/
pub trait PrimitiveTest {
    fn run(&self) -> Result<(), Error>;
}

pub trait BasicTest {
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

pub struct RunBasicTest<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test: BasicTest> PrimitiveTest for RunBasicTest<'a, Test> {
    fn run(&self) -> Result<(), Error> {
        let config = init_test()?;
        let builder = ChainBuilder::new_with_config(&config);

        info!("starting test");

        self.test.run(&config, &builder)?;

        Ok(())
    }
}
