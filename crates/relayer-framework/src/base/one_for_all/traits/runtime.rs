use async_trait::async_trait;
use core::fmt::Debug;
use core::time::Duration;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::types::runtime::LogLevel;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaBaseRuntime: Async {
    type Error: Async + Debug;

    type Time: Async;

    async fn log(&self, level: LogLevel, message: &str);

    async fn sleep(&self, duration: Duration);

    fn now(&self) -> Self::Time;

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration;
}
