use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryUnreceivedPacketSequences<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasIbcPacketTypes<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error>;
}

#[async_trait]
pub trait UnreceivedPacketsQuerier<Chain, Counterparty>
where
    Chain: HasIbcChainTypes<Counterparty> + HasIbcPacketTypes<Counterparty> + HasErrorType,
    Counterparty: HasIbcChainTypes<Chain>,
{
    async fn query_unreceived_packets(
        &self,
        channel_id: &Chain::ChannelId,
        port_id: &Chain::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Counterparty::Sequence],
        height: &Counterparty::Height,
    ) -> Result<Vec<Chain::OutgoingPacket>, Chain::Error>;
}

#[async_trait]
pub trait CanQueryUnreceivedPackets<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasIbcPacketTypes<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_unreceived_packets(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Counterparty::Sequence],
        height: &Counterparty::Height,
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error>;
}
