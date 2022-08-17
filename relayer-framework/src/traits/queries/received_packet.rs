use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::chain::IbcChainContext;

#[async_trait]
pub trait ReceivedPacketQuerier<Chain, Counterparty>
where
    Chain: IbcChainContext<Counterparty>,
    Counterparty: IbcChainContext<Chain>,
{
    async fn is_packet_received(
        chain: &Chain,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Chain::Error>;
}

#[async_trait]
pub trait HasReceivedPacketQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: IbcChainContext<Self>,
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
