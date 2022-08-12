use core::future::Future;

use crate::traits::core::Async;

pub trait CanSpawn: Async {
    fn spawn<F>(&self, task: F) -> F::Output
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;
}
