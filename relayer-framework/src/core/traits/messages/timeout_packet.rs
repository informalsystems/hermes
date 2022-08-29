use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::types::aliases::{ChannelId, Height, Message, PortId, Sequence};
use crate::std_prelude::*;

#[async_trait]
pub trait TimeoutUnorderedPacketMessageBuilder<Relay: RelayContext> {
    async fn build_timeout_unordered_packet_message(
        relay: &Relay,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
        sequence: Sequence<Relay::SrcChain, Relay::DstChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
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
