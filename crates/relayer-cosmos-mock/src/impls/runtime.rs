use async_trait::async_trait;
use ibc::core::timestamp::Timestamp;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::{sleep::CanSleep, time::HasTime};
use ibc_relayer_runtime::types::error::Error as TokioError;
use std::time::Duration;

use crate::contexts::runtime::MockRuntimeContext;

#[async_trait]
impl CanSleep for MockRuntimeContext {
    async fn sleep(&self, duration: Duration) {
        // Increment the shared MockClock by the duration is milliseconds.
        if self.clock.increment_timestamp(duration).is_err() {
            tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
        }
    }
}

impl HasTime for MockRuntimeContext {
    type Time = Timestamp;

    fn now(&self) -> Self::Time {
        self.get_time()
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Duration::from_nanos(current_time.nanoseconds() - other_time.nanoseconds())
    }
}

impl HasErrorType for MockRuntimeContext {
    type Error = TokioError;
}
