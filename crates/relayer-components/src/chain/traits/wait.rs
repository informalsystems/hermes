use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::queries::status::CanQueryChainStatus;
use crate::chain::traits::types::height::HasHeightType;
use crate::core::traits::error::HasErrorType;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

#[async_trait]
pub trait CanWaitChainSurpassHeight: HasHeightType + HasErrorType {
    async fn wait_chain_surpass_height(
        &self,
        height: &Self::Height,
    ) -> Result<Self::Height, Self::Error>;
}

#[async_trait]
impl<Chain> CanWaitChainSurpassHeight for Chain
where
    Chain: CanQueryChainStatus + HasRuntime,
    Chain::Runtime: CanSleep,
    Chain::Height: Clone,
{
    async fn wait_chain_surpass_height(
        &self,
        height: &Chain::Height,
    ) -> Result<Chain::Height, Chain::Error> {
        loop {
            let current_status = self.query_chain_status().await?;

            let current_height = Chain::chain_status_height(&current_status);

            if current_height >= height {
                return Ok(current_height.clone());
            } else {
                self.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
