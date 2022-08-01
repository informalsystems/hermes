use async_trait::async_trait;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::core::Async;

pub trait Time: Async {
    fn duration_since(&self, other: &Self) -> Duration;
}

pub trait TimeContext: Async {
    type Time: Time;

    fn now(&self) -> Self::Time;
}

#[async_trait]
pub trait SleepContext: Async {
    async fn sleep(&self, duration: Duration);
}
