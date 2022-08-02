use async_trait::async_trait;
use core::time::Duration;

use crate::one_for_all::traits::error::OfaError;
use crate::std_prelude::*;
use crate::traits::core::Async;

#[async_trait]
pub trait OfaRuntime: Clone + Async {
    type Error: OfaError;

    async fn sleep(&self, duration: Duration);
}
