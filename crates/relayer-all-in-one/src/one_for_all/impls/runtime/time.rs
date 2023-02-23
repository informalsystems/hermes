use core::time::Duration;

use crate::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::time::HasTime;

impl<Runtime: OfaBaseRuntime> HasTime for OfaRuntimeWrapper<Runtime> {
    type Time = Runtime::Time;

    fn now(&self) -> Self::Time {
        self.runtime.now()
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Runtime::duration_since(current_time, other_time)
    }
}
