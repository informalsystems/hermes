use async_trait::async_trait;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::one_for_all::error::OfaError;

#[async_trait]
pub trait OfaRuntime: Async {
    type Error: OfaError;

    async fn sleep(&self, duration: Duration);
}
