use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::core::Async;

pub trait HasConsensusState<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type ConsensusState: Async;
}

#[async_trait]
pub trait ConsensusStateQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: HasConsensusState<Self>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;
}
