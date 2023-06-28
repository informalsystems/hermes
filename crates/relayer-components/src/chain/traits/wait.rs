use async_trait::async_trait;

use crate::chain::traits::types::height::HasHeightType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanWaitChainSurpassHeight: HasHeightType + HasErrorType {
    async fn wait_chain_surpass_height(&self, height: &Self::Height) -> Result<(), Self::Error>;
}
