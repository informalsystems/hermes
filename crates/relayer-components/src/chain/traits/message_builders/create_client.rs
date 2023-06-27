use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildCreateClientMessage<Counterparty>:
    HasClientStateType<Counterparty> + HasConsensusStateType<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_create_client_message(
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
    ) -> Result<Self::Message, Self::Error>;
}
