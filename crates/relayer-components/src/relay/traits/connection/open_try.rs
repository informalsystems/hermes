use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::chains::HasRelayChains;
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenTry: HasRelayChains + HasErrorType {
    async fn relay_connection_open_try(
        &self,
        connection_id: &<Self::SrcChain as HasIbcChainTypes<Self::DstChain>>::ConnectionId,
    );
}
