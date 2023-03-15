//! The `OfaRelayWrapper` trait specifies what a relay context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseRelay`
//! trait.

use core::fmt::Debug;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::auto_relayer::AutoRelayer;
use ibc_relayer_components::relay::traits::ibc_message_sender::IbcMessageSender;
use ibc_relayer_components::relay::traits::packet_filter::PacketFilter;
use ibc_relayer_components::relay::traits::packet_relayer::PacketRelayer;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::base::one_for_all::traits::chain::OfaIbcChainPreset;
use crate::base::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

pub trait OfaRelayTypes: Async {
    type Preset: Async;

    /**
       Corresponds to [`HasErrorType::Error`](ibc_relayer_components::core::traits::error::HasErrorType).
    */
    type Error: Debug + Clone + Async;

    type Runtime: OfaBaseRuntime;

    type Logger: HasBaseLogLevels;

    type Packet: Async;

    type SrcChain: OfaIbcChain<
        Self::DstChain,
        Preset = Self::Preset,
        Logger = Self::Logger,
        OutgoingPacket = Self::Packet,
    >;

    type DstChain: OfaIbcChain<
        Self::SrcChain,
        Preset = Self::Preset,
        Logger = Self::Logger,
        IncomingPacket = Self::Packet,
        OutgoingPacket = <Self::SrcChain as OfaIbcChain<Self::DstChain>>::IncomingPacket,
    >;

    type PacketLock<'a>: Send;
}

#[async_trait]
pub trait OfaBaseRelay: OfaRelayTypes {
    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn src_chain_error(e: <Self::SrcChain as OfaChainTypes>::Error) -> Self::Error;

    fn dst_chain_error(e: <Self::DstChain as OfaChainTypes>::Error) -> Self::Error;

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

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn logger(&self) -> &Self::Logger;

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

    async fn try_acquire_packet_lock<'a>(
        &'a self,
        packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>>;
}

pub trait OfaRelayPreset<Relay>:
    OfaIbcChainPreset<Relay::SrcChain, Relay::DstChain>
    + OfaIbcChainPreset<Relay::DstChain, Relay::SrcChain>
where
    Relay: OfaBaseRelay,
{
    type AutoRelayer: AutoRelayer<OfaRelayWrapper<Relay>>;

    type PacketRelayer: PacketRelayer<OfaRelayWrapper<Relay>>;

    type PacketFilter: PacketFilter<OfaRelayWrapper<Relay>>;

    type IbcMessageSender: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

pub trait OfaHomogeneousRelay:
    OfaRelayTypes<SrcChain = Self::Chain, DstChain = Self::Chain>
{
    type Chain: OfaIbcChain<
        Self::Chain,
        IncomingPacket = Self::Packet,
        OutgoingPacket = Self::Packet,
    >;
}

impl<Relay, Chain> OfaHomogeneousRelay for Relay
where
    Relay: OfaRelayTypes<SrcChain = Chain, DstChain = Chain>,
    Chain: OfaIbcChain<Chain, IncomingPacket = Self::Packet, OutgoingPacket = Self::Packet>,
{
    type Chain = Chain;
}
