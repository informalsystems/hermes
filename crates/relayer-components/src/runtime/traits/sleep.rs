use async_trait::async_trait;
use core::time::Duration;

use crate::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait CanSleep: Async {
    async fn sleep(&self, duration: Duration);
}
