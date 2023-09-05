use async_trait::async_trait;

use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct ConsensusStateQuerierComponent;

#[async_trait]
pub trait ConsensusStateQuerier<Chain, Counterparty>
where
    Chain: HasIbcChainTypes<Counterparty> + HasErrorType,
    Counterparty: HasConsensusStateType<Chain> + HasHeightType,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error>;
}

#[async_trait]
impl<Chain, Counterparty, Component> ConsensusStateQuerier<Chain, Counterparty> for Component
where
    Chain: HasIbcChainTypes<Counterparty> + HasErrorType,
    Counterparty: HasConsensusStateType<Chain> + HasHeightType,
    Component: DelegateComponent<ConsensusStateQuerierComponent>,
    Component::Delegate: ConsensusStateQuerier<Chain, Counterparty>,
{
    async fn query_consensus_state(
        chain: &Chain,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error> {
        Component::Delegate::query_consensus_state(chain, client_id, height).await
    }
}

#[async_trait]
pub trait CanQueryConsensusState<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasErrorType
where
    Counterparty: HasConsensusStateType<Self> + HasHeightType,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;
}

#[async_trait]
impl<Chain, Counterparty> CanQueryConsensusState<Counterparty> for Chain
where
    Chain: HasIbcChainTypes<Counterparty> + HasErrorType + HasComponents,
    Counterparty: HasConsensusStateType<Self> + HasHeightType,
    Chain::Components: ConsensusStateQuerier<Chain, Counterparty>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error> {
        Chain::Components::query_consensus_state(self, client_id, height).await
    }
}
