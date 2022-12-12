use crate::base::chain::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};
use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::runtime::OfaRuntimeWrapper;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

impl<Relay: OfaBaseRelay> HasErrorType for OfaRelayWrapper<Relay> {
    type Error = Relay::Error;
}

impl<Relay: OfaBaseRelay> HasRuntime for OfaRelayWrapper<Relay> {
    type Runtime = OfaRuntimeWrapper<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Relay::Error {
        Relay::runtime_error(e)
    }
}

impl<Relay: OfaBaseRelay> HasRelayTypes for OfaRelayWrapper<Relay> {
    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

    type Packet = Relay::Packet;

    fn src_chain_error(e: <Self::SrcChain as HasErrorType>::Error) -> Self::Error {
        Relay::src_chain_error(e)
    }

    fn dst_chain_error(e: <Self::DstChain as HasErrorType>::Error) -> Self::Error {
        Relay::dst_chain_error(e)
    }

    fn packet_src_port(packet: &Self::Packet) -> &PortId<Self::SrcChain, Self::DstChain> {
        Relay::packet_src_port(packet)
    }

    fn packet_src_channel_id(packet: &Self::Packet) -> &ChannelId<Self::SrcChain, Self::DstChain> {
        Relay::packet_src_channel_id(packet)
    }

    fn packet_dst_port(packet: &Self::Packet) -> &PortId<Self::DstChain, Self::SrcChain> {
        Relay::packet_dst_port(packet)
    }

    fn packet_dst_channel_id(packet: &Self::Packet) -> &ChannelId<Self::DstChain, Self::SrcChain> {
        Relay::packet_dst_channel_id(packet)
    }

    fn packet_sequence(packet: &Self::Packet) -> &Sequence<Self::SrcChain, Self::DstChain> {
        Relay::packet_sequence(packet)
    }

    fn packet_timeout_height(packet: &Self::Packet) -> Option<&Height<Self::DstChain>> {
        Relay::packet_timeout_height(packet)
    }

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &Timestamp<Self::DstChain> {
        Relay::packet_timeout_timestamp(packet)
    }

    fn source_chain(&self) -> &Self::SrcChain {
        self.relay.src_chain()
    }

    fn destination_chain(&self) -> &Self::DstChain {
        self.relay.dst_chain()
    }

    fn source_client_id(&self) -> &<Relay::SrcChain as OfaChainTypes>::ClientId {
        self.relay.src_client_id()
    }

    fn destination_client_id(&self) -> &<Relay::DstChain as OfaChainTypes>::ClientId {
        self.relay.dst_client_id()
    }
}
