use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::time::Duration;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntime;
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::time::sleep;

use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct TokioRuntimeContext {
    pub runtime: Arc<Runtime>,
}

impl TokioRuntimeContext {
    pub fn new(runtime: Arc<Runtime>) -> Self {
        Self { runtime }
    }
}

#[async_trait]
impl OfaRuntime for TokioRuntimeContext {
    type Error = Error;

    type Time = Instant;

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }

    fn now(&self) -> Instant {
        Instant::now()
    }

    fn duration_since(time: &Instant, other: &Instant) -> Duration {
        time.duration_since(other.clone())
    }

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task);
    }
}
