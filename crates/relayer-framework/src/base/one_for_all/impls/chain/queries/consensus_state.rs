use async_trait::async_trait;

use crate::base::chain::traits::queries::consensus_state::{
    CanQueryConsensusState, ConsensusStateQuerier, HasConsensusState,
};
use crate::base::one_for_all::traits::chain::OfaBaseChain;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::traits::chain::OfaIbcChainComponents;
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct SendConsensusStateQueryToOfa;

#[async_trait]
impl<Chain, Counterparty>
    ConsensusStateQuerier<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for SendConsensusStateQueryToOfa
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
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

impl<Chain, Counterparty> HasConsensusState<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    type ConsensusState = Chain::ConsensusState;
}

#[async_trait]
impl<Chain, Counterparty, Components> CanQueryConsensusState<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty, Components = Components>,
    Counterparty: OfaIbcChain<Chain>,
    Components: OfaIbcChainComponents<Chain, Counterparty>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error> {
        Components::ConsensusStateQuerier::query_consensus_state(self, client_id, height).await
    }
}
