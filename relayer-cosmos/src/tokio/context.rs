use alloc::sync::Arc;
use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntime;
use tokio::runtime::Runtime;
use tokio::time::sleep;

use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct TokioRuntimeContext {
    pub runtime: Arc<Runtime>,
}

impl TokioRuntimeContext {
    pub fn new(runtime: Arc<Runtime>) -> Self {
        Self { runtime }
    }
}

#[async_trait]
impl OfaRuntime for TokioRuntimeContext {
    type Error = Error;

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }
}
