use core::time::Duration;

use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeWrapper};
use crate::base::runtime::traits::time::HasTime;

impl<Runtime: OfaRuntime> HasTime for OfaRuntimeWrapper<Runtime> {
    type Time = Runtime::Time;

    fn now(&self) -> Self::Time {
        let time = self.runtime.now();
        time
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Runtime::duration_since(current_time, other_time)
    }
}
