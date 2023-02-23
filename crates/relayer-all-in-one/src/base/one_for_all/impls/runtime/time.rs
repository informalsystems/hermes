use core::time::Duration;

use ibc_relayer_components::runtime::traits::time::HasTime;

use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Runtime: OfaBaseRuntime> HasTime for OfaRuntimeWrapper<Runtime> {
    type Time = Runtime::Time;

    fn now(&self) -> Self::Time {
        self.runtime.now()
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Runtime::duration_since(current_time, other_time)
    }
}
