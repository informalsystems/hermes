use async_trait::async_trait;
use ibc_relayer_components::chain::traits::components::chain_status_querier::ChainStatusQuerier;
use ibc_relayer_components::chain::traits::types::status::HasChainStatusType;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::std_prelude::*;

impl<Chain> HasChainStatusType for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    type ChainStatus = Chain::ChainStatus;

    fn chain_status_height(status: &Chain::ChainStatus) -> &Chain::Height {
        Chain::chain_status_height(status)
    }

    fn chain_status_timestamp(status: &Chain::ChainStatus) -> &Chain::Timestamp {
        Chain::chain_status_timestamp(status)
    }
}

#[async_trait]
impl<Chain> ChainStatusQuerier<OfaChainWrapper<Chain>> for OfaComponents
where
    Chain: OfaChain,
{
    async fn query_chain_status(
        context: &OfaChainWrapper<Chain>,
    ) -> Result<Chain::ChainStatus, Chain::Error> {
        let status = context.chain.query_chain_status().await?;

        Ok(status)
    }
}
