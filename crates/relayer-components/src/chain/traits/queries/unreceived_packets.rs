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
    /// Given a list of counterparty commitment sequences,
    /// return a filtered list of sequences which the chain
    /// has not received the packet from the counterparty chain.
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<Vec<Counterparty::Sequence>, Self::Error>;
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
        sequences: &[Chain::Sequence],
        height: &Chain::Height,
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
        sequences: &[Self::Sequence],
        height: &Self::Height,
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error>;
}
