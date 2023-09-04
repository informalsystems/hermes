use alloc::boxed::Box;
use alloc::sync::Arc;
use core::time::Duration;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;

use async_trait::async_trait;
use ibc_relayer_runtime::types::error::Error as TokioError;

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

impl HasErrorType for MockRuntimeContext {
    type Error = TokioError;
}

#[async_trait]
impl CanSleep for MockRuntimeContext {
    async fn sleep(&self, duration: Duration) {
        // Increment the shared MockClock by the duration is milliseconds.
        if self
            .clock
            .increment_timestamp(MockTimestamp(duration.as_millis()))
            .is_err()
        {
            tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
        }
    }
}

impl HasTime for MockRuntimeContext {
    type Time = MockTimestamp;

    fn now(&self) -> Self::Time {
        self.get_time()
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Duration::from_millis((current_time.0 - other_time.0) as u64)
    }
}
