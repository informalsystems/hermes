use core::future::Future;
use core::pin::Pin;
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

impl TaskHandle for TokioTaskHandle {
    fn abort(self: Box<Self>) {
        self.0.abort();
    }

    fn into_future(self: Box<Self>) -> Pin<Box<dyn Future<Output = ()> + Send + 'static>> {
        Box::pin(async move {
            let _ = self.0.await;
        })
    }
}
