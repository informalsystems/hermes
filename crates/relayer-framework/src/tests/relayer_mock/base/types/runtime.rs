use alloc::boxed::Box;
use async_trait::async_trait;
use core::{future::Future, time::Duration};
use std::time::Instant;
use tokio::time::sleep;

use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::{
    base::one_for_all::traits::runtime::{LogLevel, OfaRuntime},
    tests::relayer_mock::base::error::Error,
};

pub type MockRuntimeContext = TokioRuntimeContext<Error>;

#[async_trait]
impl OfaRuntime for MockRuntimeContext {
    type Error = Error;

    type Time = Instant;

    async fn log(&self, level: LogLevel, message: &str) {
        match level {
            LogLevel::Error => tracing::error!(message),
            LogLevel::Warn => tracing::warn!(message),
            LogLevel::Info => tracing::info!(message),
            LogLevel::Debug => tracing::debug!(message),
            LogLevel::Trace => tracing::trace!(message),
        }
    }

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }

    fn now(&self) -> Instant {
        Instant::now()
    }

    fn duration_since(time: &Instant, other: &Instant) -> Duration {
        time.duration_since(*other)
    }

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task);
    }
}
