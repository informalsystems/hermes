use async_trait::async_trait;

use crate::base::chain::traits::types::{HasChainTypes, HasIbcChainTypes};
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryCounterpartyChainIdFromChannel<Counterparty>:
    HasIbcChainTypes<Counterparty>
where
    Counterparty: HasChainTypes,
{
    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Counterparty::ChainId, Self::Error>;
}
