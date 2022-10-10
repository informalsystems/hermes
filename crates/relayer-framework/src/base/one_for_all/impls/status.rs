use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainContext};
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::traits::queries::status::{ChainStatusQuerier, HasChainStatus};
use crate::std_prelude::*;

pub struct OfaChainStatusQuerier;

impl<Chain: OfaChain> HasChainStatus for OfaChainContext<Chain> {
    type ChainStatus = Chain::ChainStatus;

    fn chain_status_height(status: &Chain::ChainStatus) -> &Chain::Height {
        Chain::chain_status_height(status)
    }

    fn chain_status_timestamp(status: &Chain::ChainStatus) -> &Chain::Timestamp {
        Chain::chain_status_timestamp(status)
    }
}

#[async_trait]
impl<Chain: OfaChain> ChainStatusQuerier<OfaChainContext<Chain>> for OfaChainStatusQuerier {
    async fn query_chain_status(
        context: &OfaChainContext<Chain>,
    ) -> Result<Chain::ChainStatus, OfaErrorContext<Chain::Error>> {
        let status = context.chain.query_chain_status().await?;

        Ok(status)
    }
}
