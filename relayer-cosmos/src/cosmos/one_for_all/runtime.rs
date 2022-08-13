use async_trait::async_trait;
use core::time::Duration;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntime;
use tokio::time::sleep;

use crate::cosmos::context::runtime::CosmosRuntime;
use crate::cosmos::error::Error;

#[async_trait]
impl OfaRuntime for CosmosRuntime {
    type Error = Error;

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }
}
