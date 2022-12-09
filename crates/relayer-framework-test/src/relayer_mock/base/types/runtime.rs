use alloc::boxed::Box;
use async_trait::async_trait;
use core::fmt::Debug;
use core::{future::Future, time::Duration};
use std::sync::{Arc, Mutex};
use std::{marker::PhantomData, time::Instant};

use ibc_relayer_framework::base::{
    core::traits::sync::Async,
    one_for_all::traits::runtime::{LogLevel, OfaRuntime},
};
use ibc_relayer_runtime::tokio::error::Error as TokioError;

use crate::relayer_mock;
use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::util::clock::MockClock;
use crate::relayer_mock::util::mutex::MutexUtil;

pub type MockRuntimeContext = MockChainRuntimeContext<Error>;

pub struct MockChainRuntimeContext<Error> {
    pub clock: Arc<Mutex<MockClock>>,
    pub phantom: PhantomData<Error>,
}

impl<Error: std::convert::From<relayer_mock::base::error::Error>> MockChainRuntimeContext<Error> {
    pub fn new(clock: Arc<Mutex<MockClock>>) -> Self {
        Self {
            clock,
            phantom: PhantomData,
        }
    }

    pub fn get_time(&self) -> Result<MockTimestamp, Error> {
        let clock = self.clock.acquire_mutex()?;
        let timestamp = clock.get_timestamp()?;
        Ok(timestamp)
    }
}

impl<Error: std::convert::From<relayer_mock::base::error::Error>> Clone
    for MockChainRuntimeContext<Error>
{
    fn clone(&self) -> Self {
        let clock = self.clock.clone();
        Self::new(clock)
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
        if let Ok(clock) = self.clock.acquire_mutex() {
            if clock.increment_millis(duration.as_millis()).is_err() {
                tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
            }
        }
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
        tokio::spawn(task);
    }
}
