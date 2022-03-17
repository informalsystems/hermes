use crate::framework::base::HasOverrides;

pub trait SupervisorOverride {
    fn should_spawn_supervisor(&self) -> bool;
}

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
