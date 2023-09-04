use async_trait::async_trait;

use crate::chain::types::aliases::{ChannelId, PortId};
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::sync::Async;

use crate::relay::traits::chains::HasRelayChains;
use crate::std_prelude::*;

pub struct PacketClearerComponent;

#[async_trait]
pub trait PacketClearer<Relay>: Async
where
    Relay: HasRelayChains,
{
    async fn clear_packets(
        relay: &Relay,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Relay, Component> PacketClearer<Relay> for Component
where
    Relay: HasRelayChains,
    Component: DelegateComponent<PacketClearerComponent>,
    Component::Delegate: PacketClearer<Relay>,
{
    async fn clear_packets(
        relay: &Relay,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        Component::Delegate::clear_packets(
            relay,
            src_channel_id,
            src_port_id,
            dst_channel_id,
            dst_port_id,
        )
        .await
    }
}

#[async_trait]
pub trait CanClearPackets: HasRelayChains {
    async fn clear_packets(
        &self,
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanClearPackets for Relay
where
    Relay: HasRelayChains + HasComponents,
    Relay::Components: PacketClearer<Relay>,
{
    async fn clear_packets(
        &self,
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error> {
        Relay::Components::clear_packets(
            self,
            src_channel_id,
            src_port_id,
            dst_channel_id,
            dst_port_id,
        )
        .await
    }
}
