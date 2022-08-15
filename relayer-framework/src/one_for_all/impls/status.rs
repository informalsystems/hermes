use async_trait::async_trait;

use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext};
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::std_prelude::*;
use crate::traits::queries::status::{ChainStatus, ChainStatusContext, ChainStatusQuerier};

pub struct OfaChainStatusQuerier;

pub struct OfaChainStatus<Chain: OfaChain> {
    pub status: Chain::ChainStatus,
}

impl<Chain: OfaChain> ChainStatusContext for OfaChainContext<Chain> {
    type ChainStatus = OfaChainStatus<Chain>;
}

impl<Chain: OfaChain> ChainStatus<OfaChainContext<Chain>> for OfaChainStatus<Chain> {
    fn height(&self) -> &Chain::Height {
        Chain::chain_status_height(&self.status)
    }

    fn timestamp(&self) -> &Chain::Timestamp {
        Chain::chain_status_timestamp(&self.status)
    }
}

#[async_trait]
impl<Chain: OfaChain> ChainStatusQuerier<OfaChainContext<Chain>> for OfaChainStatusQuerier {
    async fn query_chain_status(
        context: &OfaChainContext<Chain>,
    ) -> Result<OfaChainStatus<Chain>, OfaErrorContext<Chain::Error>> {
        let status = context.chain.query_chain_status().await?;

        Ok(OfaChainStatus { status })
    }
}
