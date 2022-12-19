use core::future::Future;

use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::full::one_for_all::traits::runtime::OfaFullRuntime;
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

impl<Runtime: OfaFullRuntime> HasSpawner for OfaRuntimeWrapper<Runtime> {
    type Spawner = Self;

    fn spawner(&self) -> Self::Spawner {
        self.clone()
    }
}

impl<Runtime: OfaFullRuntime> Spawner for OfaRuntimeWrapper<Runtime> {
    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task)
    }
}
