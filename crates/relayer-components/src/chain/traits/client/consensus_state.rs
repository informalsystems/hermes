use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildConsensusState<Counterparty>:
    HasConsensusStateType<Counterparty> + HasClientStateType<Counterparty> + HasErrorType
{
    async fn build_consensus_state(
        trusted_height: &Self::Height,
        target_height: &Self::Height,
        client_state: &Self::ClientState,
    ) -> Result<Self::ConsensusState, Self::Error>;
}
