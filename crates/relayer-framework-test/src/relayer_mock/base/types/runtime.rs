use alloc::boxed::Box;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaBaseRuntime;
use ibc_relayer_framework::base::one_for_all::types::runtime::LogLevel;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use tokio::sync::{Mutex, MutexGuard};

use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::util::clock::MockClock;

pub struct MockRuntimeContext {
    pub clock: Arc<MockClock>,
}

impl MockRuntimeContext {
    pub fn new(clock: Arc<MockClock>) -> Self {
        Self { clock }
    }

    pub fn get_time(&self) -> MockTimestamp {
        self.clock.get_timestamp()
    }
}

impl Clone for MockRuntimeContext {
    fn clone(&self) -> Self {
        let clock = self.clock.clone();
        Self::new(clock)
    }
}

#[async_trait]
impl OfaBaseRuntime for MockRuntimeContext {
    type Error = TokioError;

    type Time = MockTimestamp;

    type Mutex<T: Async> = Mutex<T>;

    type MutexGuard<'a, T: Async> = MutexGuard<'a, T>;

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
        if self
            .clock
            .increment_timestamp(MockTimestamp(duration.as_millis()))
            .is_err()
        {
            tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
        }
    }

    fn now(&self) -> Self::Time {
        self.get_time()
    }

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration {
        Duration::from_millis((time.0 - other.0) as u64)
    }

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T> {
        Mutex::new(item)
    }

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T> {
        mutex.lock().await
    }
}
