use async_trait::async_trait;
use ibc_relayer_components::chain::traits::queries::consensus_state::{
    CanQueryConsensusState, ConsensusStateQuerier,
};
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasConsensusStateType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ConsensusState = Chain::ConsensusState;
}

pub struct SendConsensusStateQueryToOfa;

#[async_trait]
impl<Chain, Counterparty>
    ConsensusStateQuerier<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for SendConsensusStateQueryToOfa
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn query_consensus_state(
        chain: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error> {
        let consensus_state = chain.chain.query_consensus_state(client_id, height).await?;

        Ok(consensus_state)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQueryConsensusState<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error> {
        components::ConsensusStateQuerier::query_consensus_state(self, client_id, height).await
    }
}
