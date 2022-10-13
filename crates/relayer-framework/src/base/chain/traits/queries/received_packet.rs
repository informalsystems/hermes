use async_trait::async_trait;

use crate::base::chain::traits::context::HasIbcChainTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait ReceivedPacketQuerier<Chain, Counterparty>
where
    Chain: HasIbcChainTypes<Counterparty>,
    Counterparty: HasIbcChainTypes<Chain>,
{
    async fn is_packet_received(
        chain: &Chain,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Chain::Error>;
}

#[async_trait]
pub trait HasReceivedPacketQuerier<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    type ReceivedPacketQuerier: ReceivedPacketQuerier<Self, Counterparty>;

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error> {
        Self::ReceivedPacketQuerier::is_packet_received(self, port_id, channel_id, sequence).await
    }
}
