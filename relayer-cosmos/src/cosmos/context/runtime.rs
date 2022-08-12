use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_framework::traits::contexts::error::ErrorContext;
use ibc_relayer_framework::traits::runtime::sleep::SleepContext;
use tokio::time::sleep;

use crate::cosmos::error::Error;

pub struct CosmosRuntimeContext;

#[async_trait]
impl SleepContext for CosmosRuntimeContext {
    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }
}

impl ErrorContext for CosmosRuntimeContext {
    type Error = Error;
}
