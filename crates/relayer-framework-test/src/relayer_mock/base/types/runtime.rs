use alloc::boxed::Box;
use async_trait::async_trait;
use core::fmt::Debug;
use core::{future::Future, time::Duration};
use std::{marker::PhantomData, time::Instant};
use tokio::{runtime::Runtime, time::sleep};

use ibc_relayer_framework::base::{
    core::traits::sync::Async,
    one_for_all::traits::runtime::{LogLevel, OfaRuntime},
};

use crate::relayer_mock::base::error::Error;

use ibc_relayer_runtime::tokio::error::Error as TokioError;

pub type MockRuntimeContext = MockChainRuntimeContext<Error>;

pub struct MockChainRuntimeContext<Error> {
    pub phantom: PhantomData<Error>,
}

impl Default for MockChainRuntimeContext<Error> {
    fn default() -> Self {
        Self { phantom: Default::default() }
    }
}

impl<Error> MockChainRuntimeContext<Error> {
    pub fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<Error> Clone for MockChainRuntimeContext<Error> {
    fn clone(&self) -> Self {
        Self::new()
    }
}

#[async_trait]
impl OfaRuntime for MockRuntimeContext
where
    Error: From<TokioError> + Debug + Async,
{
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
        let runtime = Runtime::new().unwrap();
        runtime.spawn(task);
    }
}
