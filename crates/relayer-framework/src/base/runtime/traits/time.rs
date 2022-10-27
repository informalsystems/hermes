use core::time::Duration;

use crate::base::core::traits::sync::Async;

pub trait Time: Async {
    fn duration_since(&self, other: &Self) -> Duration;
}

pub trait HasTime: Async {
    type Time: Time;

    fn now(&self) -> Self::Time;
}
