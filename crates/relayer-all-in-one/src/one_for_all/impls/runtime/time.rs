use core::time::Duration;

use ibc_relayer_components::runtime::traits::time::HasTime;

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

impl<Runtime> HasTime for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    type Time = Runtime::Time;

    fn now(&self) -> Self::Time {
        self.runtime.now()
    }

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration {
        Runtime::duration_since(current_time, other_time)
    }
}
