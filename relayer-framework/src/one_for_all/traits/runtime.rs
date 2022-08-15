use async_trait::async_trait;
use core::time::Duration;

use crate::one_for_all::traits::error::OfaError;
use crate::std_prelude::*;
use crate::traits::core::Async;

#[derive(Clone)]
pub struct OfaRuntimeContext<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeContext<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
}

#[async_trait]
pub trait OfaRuntime: Clone + Async {
    type Error: OfaError;

    async fn sleep(&self, duration: Duration);
}
