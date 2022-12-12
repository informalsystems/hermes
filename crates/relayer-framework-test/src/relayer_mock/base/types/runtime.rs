use alloc::boxed::Box;
use async_trait::async_trait;
use core::{future::Future, time::Duration};
use std::sync::Arc;
use std::time::Instant;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::util::clock::MockClock;

use ibc_relayer_framework::base::one_for_all::traits::runtime::{LogLevel, OfaRuntime};
use ibc_relayer_runtime::tokio::error::Error as TokioError;

pub struct MockRuntimeContext {
    pub clock: Arc<MockClock>,
}

impl MockRuntimeContext {
    pub fn new(clock: Arc<MockClock>) -> Self {
        Self { clock }
    }

    pub fn get_time(&self) -> Result<MockTimestamp, Error> {
        let timestamp = self.clock.get_timestamp()?;
        Ok(timestamp)
    }
}

impl Clone for MockRuntimeContext {
    fn clone(&self) -> Self {
        let clock = self.clock.clone();
        Self::new(clock)
    }
}

#[async_trait]
impl OfaRuntime for MockRuntimeContext {
    type Error = TokioError;

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

    // Increment the shared MockClock by the duration is milliseconds.
    async fn sleep(&self, duration: Duration) {
        if self.clock.increment_millis(duration.as_millis()).is_err() {
            tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
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
