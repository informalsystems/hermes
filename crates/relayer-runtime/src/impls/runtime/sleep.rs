use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use tokio::time::sleep;

use crate::types::runtime::TokioRuntimeContext;

#[async_trait]
impl CanSleep for TokioRuntimeContext {
    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }
}
