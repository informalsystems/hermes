use async_trait::async_trait;

use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::component::HasComponents;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

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

#[macro_export]
macro_rules! derive_consensus_state_querier {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Chain, Counterparty, $( $( $param ),* )*>
            $crate::chain::traits::queries::consensus_state::ConsensusStateQuerier<Chain, Counterparty>
            for $target $( < $( $param ),* > )*
        where
            Chain:
                $crate::chain::traits::types::ibc::HasIbcChainTypes<Counterparty>
                + $crate::core::traits::error::HasErrorType,
            Counterparty:
                $crate::chain::traits::types::consensus_state::HasConsensusStateType<Chain>
                + $crate::chain::traits::types::height::HasHeightType,
            $source: $crate::chain::traits::queries::consensus_state::ConsensusStateQuerier<Chain, Counterparty>,
        {
            async fn query_consensus_state(
                chain: &Chain,
                client_id: &Chain::ClientId,
                height: &Counterparty::Height,
            ) -> Result<Counterparty::ConsensusState, Chain::Error> {
                <$source as $crate::chain::traits::queries::consensus_state::ConsensusStateQuerier<Chain, Counterparty>>
                    ::query_consensus_state(chain, client_id, height).await
            }
        }
    };
}
