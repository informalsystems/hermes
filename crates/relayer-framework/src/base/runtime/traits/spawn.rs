use core::future::Future;

use crate::base::core::traits::sync::Async;

pub trait HasSpawner: Async {
    type Spawner: Spawner;

    fn spawner(&self) -> Self::Spawner;
}

pub trait Spawner: Async {
    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;
}
