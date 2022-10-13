use async_trait::async_trait;

use crate::base::chain::types::aliases::{ChannelId, Height, Message, PortId};
use crate::base::relay::traits::context::HasRelayTypes;
use crate::std_prelude::*;

/// Encapsulates the capability of the implementer to construct a timeout
/// message that gets sent over an unordered channel from a destination chain
/// to the source chain that originated the message that has timed out.
#[async_trait]
pub trait TimeoutUnorderedPacketMessageBuilder<Relay: HasRelayTypes> {
    async fn build_timeout_unordered_packet_message(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

/// A type that implements this trait has the capability to construct a
/// timeout message that gets sent over an unordered channel from a
/// destination chain to the source chain that originated the timed out message.
#[async_trait]
pub trait HasTimeoutUnorderedPacketMessageBuilder: HasRelayTypes {
    type TimeoutUnorderedPacketMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Self>;

    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<Message<Self::SrcChain>, Self::Error> {
        Self::TimeoutUnorderedPacketMessageBuilder::build_timeout_unordered_packet_message(
            self,
            destination_height,
            packet,
        )
        .await
    }
}

#[async_trait]
pub trait TimeoutOrderedPacketMessageBuilder<Relay: HasRelayTypes> {
    async fn build_timeout_ordered_packet_message(
        context: &Relay,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

#[async_trait]
pub trait TimeoutChannelClosedMessageBuilder<Relay: HasRelayTypes> {
    async fn build_timeout_channel_closed_message(
        context: &Relay,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}
