use core::future::Future;

use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeWrapper};
use crate::base::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

impl<Runtime: OfaRuntime> HasSpawner for OfaRuntimeWrapper<Runtime> {
    type Spawner = Self;

    fn spawner(&self) -> Self::Spawner {
        self.clone()
    }
}

impl<Runtime: OfaRuntime> Spawner for OfaRuntimeWrapper<Runtime> {
    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task)
    }
}
