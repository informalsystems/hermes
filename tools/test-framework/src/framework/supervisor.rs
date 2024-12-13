/**
   Constructs for wrapping test cases to spawn the relayer supervisor
   before the inner test is executed.
*/
use crate::framework::base::HasOverrides;

/**
   An internal trait that can be implemented by test cases to override
   whether to automatically spawn the relayer supervisor before the
   test starts.

   This is used by [`RunWithSupervisor`] to determine whether to
   spawn the relayer.

  Test writers should implement
  [`TestOverrides`](crate::framework::overrides::TestOverrides)
  for their test cases instead of implementing this trait directly.
*/
pub trait SupervisorOverride {
    fn should_spawn_supervisor(&self) -> bool;
}

/**
   A wrapper type that implements the same test traits as the wrapped
   `Test` type, and spawns the relayer supervisor before the inner test
   is called.

   For example, if `Test` implements
   [`BinaryChannelTest`](crate::framework::binary::channel::BinaryChannelTest),
   then `RunWithSupervisor<Test>` also implements `BinaryChannelTest`.

   The automatic spawning of supervisor can be disabled by implementing
   [`SupervisorOverride`] and returning false.

   When composing the test runners with `RunWithSupervisor`, it is important
   to ensure that `RunWithSupervisor` do not appear more than once in the
   nesting. Otherwise the supervisor may spawn more than once during tests.
*/
pub struct RunWithSupervisor<'a, Test> {
    pub test: &'a Test,
}

impl<'a, Test> RunWithSupervisor<'a, Test> {
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> HasOverrides for RunWithSupervisor<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
