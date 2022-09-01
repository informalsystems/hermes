use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::types::aliases::{ChannelId, Height, Message, PortId};
use crate::std_prelude::*;

/// Encapsulates the capability of the implementer to construct a timeout
/// message that gets sent over an unordered channel from the destination
/// chain to the source chain.
#[async_trait]
pub trait TimeoutUnorderedPacketMessageBuilder<Relay: RelayContext> {
    async fn build_timeout_unordered_packet_message(
        relay: &Relay,
        height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

/// A type that implements this trait has the capability to construct a 
/// timeout message that gets sent over an unordered channel from the 
/// destination chain to the source chain.
#[async_trait]
pub trait HasTimeoutUnorderedPacketMessageBuilder: RelayContext {
    type TimeoutUnorderedPacketMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Self>;

    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<Message<Self::SrcChain>, Self::Error> {
        Self::TimeoutUnorderedPacketMessageBuilder::build_timeout_unordered_packet_message(self, height, packet).await
    }
}

#[async_trait]
pub trait TimeoutOrderedPacketMessageBuilder<Relay: RelayContext> {
    async fn build_timeout_ordered_packet_message(
        relay: &Relay,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

#[async_trait]
pub trait TimeoutChannelClosedMessageBuilder<Relay: RelayContext> {
    async fn build_timeout_channel_closed_message(
        relay: &Relay,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}
