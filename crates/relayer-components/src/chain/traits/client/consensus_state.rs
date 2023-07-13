use async_trait::async_trait;

use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanFindConsensusStateHeight<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasErrorType
where
    Counterparty: HasHeightType,
{
    /**
       Query the chain to find a consensus state that has a height that is
       less than or equal the target height. This is needed as a base trusted
       height to build the headers for UpdateClient.

       Invariant: the returned height must be less than or equal to the given
       target height.
    */
    async fn find_consensus_state_height_before(
        &self,
        client_id: &Self::ClientId,
        target_height: &Counterparty::Height,
    ) -> Result<Counterparty::Height, Self::Error>;
}
