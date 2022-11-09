//! The `OfaRelayWrapper` trait specifies what a relay context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseRelay`
//! trait.

use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::chain::OfaIbcChainPreset;
use crate::base::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::base::one_for_all::traits::runtime::OfaRuntime;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

pub trait OfaRelayTypes: Async {
    type Preset;

    /**
       Corresponds to [`HasError::Error`](crate::base::core::traits::error::HasError).
    */
    type Error: Async + Debug;

    type Runtime: OfaRuntime<Error = Self::Error>;

    type Packet: Async;

    type SrcChain: OfaIbcChain<
        Self::DstChain,
        Error = Self::Error,
        Runtime = Self::Runtime,
        Preset = Self::Preset,
    >;

    type DstChain: OfaIbcChain<
        Self::SrcChain,
        Error = Self::Error,
        Runtime = Self::Runtime,
        Preset = Self::Preset,
    >;
}

#[async_trait]
pub trait OfaBaseRelay: OfaRelayTypes {
    fn is_retryable_error(e: &Self::Error) -> bool;

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error;

    fn mismatch_ibc_events_count_error(expected: usize, actual: usize) -> Self::Error;

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

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain>;

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain>;

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

pub trait OfaRelayPreset<Relay>:
    OfaIbcChainPreset<Relay::SrcChain, Relay::DstChain>
    + OfaIbcChainPreset<Relay::DstChain, Relay::SrcChain>
where
    Relay: OfaBaseRelay,
{
    type PacketRelayer: PacketRelayer<OfaRelayWrapper<Relay>>;

    type IbcMessageSender: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}
