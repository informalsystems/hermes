use async_trait::async_trait;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::core::Async;

#[async_trait]
pub trait CanSleep: Async {
    async fn sleep(&self, duration: Duration);
}
