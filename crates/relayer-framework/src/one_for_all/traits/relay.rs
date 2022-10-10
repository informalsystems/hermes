//! The `OfaRelayContext` trait specifies what a relay context needs to provide
//! in order to gain access to the APIs provided by the [`AfoRelayContext`]
//! trait.

use async_trait::async_trait;

use crate::core::traits::core::Async;
use crate::one_for_all::traits::chain::{OfaChainContext, OfaChainTypes, OfaIbcChain};
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaRelayContext<Relay> {
    pub relay: Relay,
}

impl<Relay: OfaRelay> OfaRelayContext<Relay> {
    pub fn new(relay: Relay) -> Self {
        Self { relay }
    }
}

#[async_trait]
pub trait OfaRelay: Async {
    type Components;

    type Error: OfaError;

    type Runtime: OfaRuntime<Error = Self::Error>;

    type SrcChain: OfaIbcChain<
        Self::DstChain,
        Error = Self::Error,
        Runtime = Self::Runtime,
        Components = Self::Components,
    >;

    type DstChain: OfaIbcChain<
        Self::SrcChain,
        Error = Self::Error,
        Runtime = Self::Runtime,
        Components = Self::Components,
    >;

    type Packet: Async;

    type Telemetry: Async;

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::PortId;

    fn packet_src_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::SrcChain as OfaChainTypes>::ChannelId;

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChainTypes>::PortId;

    fn packet_dst_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::ChannelId;

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::Sequence;

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChainTypes>::Height>;

    fn packet_timeout_timestamp(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::Timestamp;

    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime>;

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChainTypes>::ClientId;

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId;

    fn src_chain(&self) -> &OfaChainContext<Self::SrcChain>;

    fn dst_chain(&self) -> &OfaChainContext<Self::DstChain>;

    fn telemetry(&self) -> &Self::Telemetry;

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChainTypes>::Message>, Self::Error>;

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChainTypes>::Message>, Self::Error>;

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChainTypes>::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        ack: &<Self::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error>;

    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error>;
}
