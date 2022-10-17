use async_trait::async_trait;

use crate::base::chain::traits::types::{HasChainTypes, HasIbcChainTypes};
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasConsensusState<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasChainTypes,
{
    type ConsensusState: Async;
}

#[async_trait]
pub trait ConsensusStateQuerier<Chain, Counterparty>
where
    Chain: HasIbcChainTypes<Counterparty>,
    Counterparty: HasConsensusState<Chain>,
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
    Counterparty: HasConsensusState<Self>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;
}
