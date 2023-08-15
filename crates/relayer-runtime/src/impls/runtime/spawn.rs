use core::future::Future;
use ibc_relayer_components_extra::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};

use crate::types::runtime::TokioRuntimeContext;
use crate::types::task::TokioTaskHandle;

impl HasSpawner for TokioRuntimeContext {
    type Spawner = Self;

    fn spawner(&self) -> Self::Spawner {
        self.clone()
    }
}

impl Spawner for TokioRuntimeContext {
    fn spawn<F>(&self, task: F) -> Box<dyn TaskHandle>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let join_handle = self.runtime.spawn(async move {
            task.await;
        });
        Box::new(TokioTaskHandle(join_handle))
    }
}
