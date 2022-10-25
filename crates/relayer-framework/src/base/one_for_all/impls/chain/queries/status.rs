use async_trait::async_trait;

use crate::base::chain::traits::queries::status::{
    CanQueryChainStatus, ChainStatusQuerier, HasChainStatus,
};
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainPreset};
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct SendChainStatusQueryToOfa;

impl<Chain: OfaBaseChain> HasChainStatus for OfaChainWrapper<Chain> {
    type ChainStatus = Chain::ChainStatus;

    fn chain_status_height(status: &Chain::ChainStatus) -> &Chain::Height {
        Chain::chain_status_height(status)
    }

    fn chain_status_timestamp(status: &Chain::ChainStatus) -> &Chain::Timestamp {
        Chain::chain_status_timestamp(status)
    }
}

#[async_trait]
impl<Chain: OfaBaseChain> ChainStatusQuerier<OfaChainWrapper<Chain>> for SendChainStatusQueryToOfa {
    async fn query_chain_status(
        context: &OfaChainWrapper<Chain>,
    ) -> Result<Chain::ChainStatus, Chain::Error> {
        let status = context.chain.query_chain_status().await?;

        Ok(status)
    }
}

#[async_trait]
impl<Chain, Preset> CanQueryChainStatus for OfaChainWrapper<Chain>
where
    Chain: OfaBaseChain<Preset = Preset>,
    Preset: OfaChainPreset<Chain>,
{
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Preset::ChainStatusQuerier::query_chain_status(self).await
    }
}
