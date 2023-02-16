use async_trait::async_trait;

use crate::base::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait ConsensusStateQuerier<Chain, Counterparty>
where
    Chain: HasIbcChainTypes<Counterparty>,
    Counterparty: HasConsensusStateType<Chain>,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error>;
}

#[async_trait]
pub trait CanQueryConsensusState<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasConsensusStateType<Self>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;
}
