//! The `OfaRelayWrapper` trait specifies what a relay context needs to provide
//! in order to gain access to the APIs provided by the [`AfoBaseRelay`]
//! trait.

use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::chain::{OfaBaseChainTypes, OfaIbcChain};
use crate::base::one_for_all::traits::error::OfaError;
use crate::base::one_for_all::traits::runtime::OfaRuntime;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub trait OfaRelayTypes: Async {
    type Components;

    type Error: OfaError;

    type Runtime: OfaRuntime<Error = Self::Error>;

    type Packet: Async;

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
}

#[async_trait]
pub trait OfaBaseRelay: OfaRelayTypes {
    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaBaseChainTypes>::PortId;

    fn packet_src_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::SrcChain as OfaBaseChainTypes>::ChannelId;

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaBaseChainTypes>::PortId;

    fn packet_dst_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaBaseChainTypes>::ChannelId;

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaBaseChainTypes>::Sequence;

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaBaseChainTypes>::Height>;

    fn packet_timeout_timestamp(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaBaseChainTypes>::Timestamp;

    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime>;

    fn src_client_id(&self) -> &<Self::SrcChain as OfaBaseChainTypes>::ClientId;

    fn dst_client_id(&self) -> &<Self::DstChain as OfaBaseChainTypes>::ClientId;

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain>;

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain>;

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaBaseChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaBaseChainTypes>::Message>, Self::Error>;

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaBaseChainTypes>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaBaseChainTypes>::Message>, Self::Error>;

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaBaseChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaBaseChainTypes>::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaBaseChainTypes>::Height,
        packet: &Self::Packet,
        ack: &<Self::DstChain as OfaBaseChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaBaseChainTypes>::Message, Self::Error>;

    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaBaseChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaBaseChainTypes>::Message, Self::Error>;
}
