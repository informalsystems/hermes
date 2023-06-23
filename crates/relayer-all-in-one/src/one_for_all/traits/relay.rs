//! The `OfaRelayWrapper` trait specifies what a relay context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseRelay`
//! trait.

use core::fmt::Debug;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;

use crate::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaRelay: Async {
    /**
       Corresponds to [`HasErrorType::Error`](ibc_relayer_components::core::traits::error::HasErrorType).
    */
    type Error: Debug + Clone + Async;

    type Runtime: OfaRuntime;

    type Logger: HasBaseLogLevels;

    type Packet: Async;

    type SrcChain: OfaIbcChain<Self::DstChain, Logger = Self::Logger, OutgoingPacket = Self::Packet>;

    type DstChain: OfaIbcChain<
        Self::SrcChain,
        Logger = Self::Logger,
        IncomingPacket = Self::Packet,
        OutgoingPacket = <Self::SrcChain as OfaIbcChain<Self::DstChain>>::IncomingPacket,
    >;

    type PacketLock<'a>: Send;

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error;

    fn src_chain_error(e: <Self::SrcChain as OfaChain>::Error) -> Self::Error;

    fn dst_chain_error(e: <Self::DstChain as OfaChain>::Error) -> Self::Error;

    fn is_retryable_error(e: &Self::Error) -> bool;

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error;

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::PortId;

    fn packet_src_channel_id(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::ChannelId;

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::PortId;

    fn packet_dst_channel_id(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::ChannelId;

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::Sequence;

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChain>::Height>;

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::Timestamp;

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn logger(&self) -> &Self::Logger;

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChain>::ClientId;

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChain>::ClientId;

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain>;

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain>;

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChain>::Message>, Self::Error>;

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChain>::Message>, Self::Error>;

    async fn try_acquire_packet_lock<'a>(
        &'a self,
        packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>>;

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;

    fn src_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error>;

    fn dst_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error>;
}

pub trait OfaHomogeneousRelay: OfaRelay<SrcChain = Self::Chain, DstChain = Self::Chain> {
    type Chain: OfaIbcChain<
        Self::Chain,
        IncomingPacket = Self::Packet,
        OutgoingPacket = Self::Packet,
    >;
}

impl<Relay, Chain> OfaHomogeneousRelay for Relay
where
    Relay: OfaRelay<SrcChain = Chain, DstChain = Chain>,
    Chain: OfaIbcChain<Chain, IncomingPacket = Self::Packet, OutgoingPacket = Self::Packet>,
{
    type Chain = Chain;
}
