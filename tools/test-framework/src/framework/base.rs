/*!
    Base infrastructure for the test framework. Includes basic setup for
    initializing the logger and loading the test configuration.
*/

use tracing::info;

use crate::bootstrap::init::init_test;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::types::config::TestConfig;

/**
   Runs a primitive test case implementing [`PrimitiveTest`].
*/
pub fn run_test<Test: PrimitiveTest>(test: &Test) -> Result<(), Error> {
    test.run()
}

/**
   Runs a basic test case implementing [`BasicTest`].
*/
pub fn run_basic_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BasicTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride,
{
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
    /**
       The inner type that implements the override traits.
    */
    type Overrides;

    /**
       Get the reference to the inner override type.
    */
    fn get_overrides(&self) -> &Self::Overrides;
}

/**
   A primitive test case provides no additional logic.
*/
pub trait PrimitiveTest {
    /// Test runner
    fn run(&self) -> Result<(), Error>;
}

/**
   A basic test has the minimal test setup that is essential for almost all
   tests.

   The test runner is given a [`TestConfig`] and [`ChainBuilder`], which
   provides the essential customization for how the tests should be run.
*/
pub trait BasicTest {
    /// Test runner
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error>;
}

pub trait TestConfigOverride {
    fn modify_test_config(&self, config: &mut TestConfig);
}

/**
   A wrapper type that lifts a test case that implements [`BasicTest`]
   into a test case that implements [`PrimitiveTest`].
*/
pub struct RunBasicTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, Overrides> PrimitiveTest for RunBasicTest<'a, Test>
where
    Test: BasicTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride,
{
    fn run(&self) -> Result<(), Error> {
        let mut config = init_test()?;
        self.test.get_overrides().modify_test_config(&mut config);

        info!("starting test with test config: {:?}", config);

        let builder = ChainBuilder::new_with_config(&config);

        self.test.run(&config, &builder)?;

        Ok(())
    }
}
