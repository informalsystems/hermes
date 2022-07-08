use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::Async;

pub trait ConsensusStateContext<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type ConsensusState: Async;
}

#[async_trait]
pub trait ConsensusStateQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ConsensusStateContext<Self>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;
}
