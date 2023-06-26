use core::future::Future;

use ibc_relayer_components_extra::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

impl<Runtime: OfaRuntime> HasSpawner for OfaRuntimeWrapper<Runtime> {
    type Spawner = Self;

    fn spawner(&self) -> Self::Spawner {
        self.clone()
    }
}

impl<Runtime: OfaRuntime> Spawner for OfaRuntimeWrapper<Runtime> {
    fn spawn<F>(&self, task: F) -> Box<dyn TaskHandle>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task)
    }
}
