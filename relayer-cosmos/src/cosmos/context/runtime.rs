use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_framework::traits::contexts::error::HasError;
use ibc_relayer_framework::traits::runtime::sleep::CanSleep;
use tokio::time::sleep;

use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct CosmosRuntime;

#[async_trait]
impl CanSleep for CosmosRuntime {
    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }
}

impl HasError for CosmosRuntime {
    type Error = Error;
}
