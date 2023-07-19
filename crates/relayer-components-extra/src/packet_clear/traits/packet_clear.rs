use async_trait::async_trait;
use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::relay::traits::packet::HasRelayPacket;

use crate::std_prelude::*;

#[async_trait]
pub trait CanClearPackets: HasRelayPacket {
    async fn clear_receive_packets(
        &self,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait PacketClearer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn clear_receive_packets(
        relay: &Relay,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
    ) -> Result<(), Relay::Error>;
}
