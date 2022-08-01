use async_trait::async_trait;
use core::time::Duration;

use crate::std_prelude::*;

#[async_trait]
pub trait SleepContext {
    async fn sleep(&self, duration: Duration);
}
