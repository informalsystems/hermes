use crate::base::chain::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::runtime::HasRuntime;
use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

impl<Relay: OfaBaseRelay> HasError for OfaRelayWrapper<Relay> {
    type Error = Relay::Error;
}

impl<Relay: OfaBaseRelay> HasRuntime for OfaRelayWrapper<Relay> {
    type Runtime = OfaRuntimeContext<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }
}

impl<Relay: OfaBaseRelay> HasRelayTypes for OfaRelayWrapper<Relay> {
    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

    type Packet = Relay::Packet;

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
