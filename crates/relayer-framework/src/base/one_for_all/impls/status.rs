use async_trait::async_trait;

use crate::base::chain::traits::queries::status::{ChainStatusQuerier, HasChainStatus};
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainWrapper};
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::std_prelude::*;

pub struct OfaBaseChainStatusQuerier;

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
impl<Chain: OfaBaseChain> ChainStatusQuerier<OfaChainWrapper<Chain>> for OfaBaseChainStatusQuerier {
    async fn query_chain_status(
        context: &OfaChainWrapper<Chain>,
    ) -> Result<Chain::ChainStatus, OfaErrorContext<Chain::Error>> {
        let status = context.chain.query_chain_status().await?;

        Ok(status)
    }
}
