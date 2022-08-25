use async_trait::async_trait;

use crate::core::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::core::traits::core::Async;
use crate::std_prelude::*;

pub trait HasConsensusState<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type ConsensusState: Async;
}

#[async_trait]
pub trait ConsensusStateQuerier<Chain, Counterparty>
where
    Chain: IbcChainContext<Counterparty>,
    Counterparty: HasConsensusState<Chain>,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error>;
}

#[async_trait]
pub trait HasConsensusStateQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: HasConsensusState<Self>,
{
    type ConsensusStateQuerier: ConsensusStateQuerier<Self, Counterparty>;

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error> {
        Self::ConsensusStateQuerier::query_consensus_state(self, client_id, height).await
    }
}
