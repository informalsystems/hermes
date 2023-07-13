use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CommitmentsPacketQuerier<Chain, Counterparty>
where
    Chain: HasIbcPacketTypes<Counterparty> + HasErrorType,
    Counterparty: HasIbcChainTypes<Chain>,
{
    async fn query_packet_commitments(
        chain: &Chain,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
    ) -> Result<Chain::Sequence, Chain::Error>;
}

#[async_trait]
pub trait CanQueryPacketCommitments<Counterparty>:
    HasIbcPacketTypes<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_packet_commitments(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Vec<Self::Sequence>, Self::Error>;
}
