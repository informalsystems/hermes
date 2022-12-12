use core::time::Duration;

use crate::base::core::traits::sync::Async;

pub trait HasTime: Async {
    type Time: Async;

    fn now(&self) -> Self::Time;

    fn duration_since(current_time: &Self::Time, other_time: &Self::Time) -> Duration;
}
