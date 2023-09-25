use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::components::chain_status_querier::CanQueryChainHeight;
use crate::chain::traits::types::height::HasHeightType;
use crate::core::traits::error::HasErrorType;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

#[async_trait]
pub trait CanWaitChainReachHeight: HasHeightType + HasErrorType {
    async fn wait_chain_reach_height(
        &self,
        height: &Self::Height,
    ) -> Result<Self::Height, Self::Error>;
}

#[async_trait]
impl<Chain> CanWaitChainReachHeight for Chain
where
    Chain: CanQueryChainHeight + HasRuntime,
    Chain::Runtime: CanSleep,
    Chain::Height: Clone,
{
    async fn wait_chain_reach_height(
        &self,
        height: &Chain::Height,
    ) -> Result<Chain::Height, Chain::Error> {
        loop {
            let current_height = self.query_chain_height().await?;

            if &current_height >= height {
                return Ok(current_height.clone());
            } else {
                self.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
