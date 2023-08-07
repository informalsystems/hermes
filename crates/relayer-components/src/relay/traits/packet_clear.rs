use async_trait::async_trait;

use crate::chain::types::aliases::{ChannelId, PortId};
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;

use crate::std_prelude::*;

#[async_trait]
pub trait CanClearReceivePackets: HasRelayPacket {
    async fn clear_receive_packets(
        &self,
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ReceivePacketClearer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn clear_receive_packets(
        relay: &Relay,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}
