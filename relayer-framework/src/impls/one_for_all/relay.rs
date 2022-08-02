use crate::impls::one_for_all::chain::OfaChainContext;
use crate::impls::one_for_all::error::OfaErrorContext;
use crate::impls::one_for_all::message::OfaMessage;
use crate::impls::one_for_all::runtime::OfaRuntimeContext;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::ErrorContext;
use crate::traits::one_for_all::chain::OfaChain;
use crate::traits::one_for_all::relay::OfaRelay;
use crate::traits::packet::IbcPacket;
use crate::traits::relay_context::RelayContext;
use crate::traits::runtime::context::RuntimeContext;

pub struct OfaRelayContext<Relay: OfaRelay> {
    pub src_chain: OfaChainContext<Relay::SrcChain>,
    pub dst_chain: OfaChainContext<Relay::DstChain>,

    pub src_client_id: <Relay::SrcChain as OfaChain>::ClientId,
    pub dst_client_id: <Relay::DstChain as OfaChain>::ClientId,

    pub runtime: OfaRuntimeContext<Relay::Runtime>,
}

pub struct OfaPacket<Relay: OfaRelay> {
    pub packet: Relay::Packet,
}

impl<Relay: OfaRelay> ErrorContext for OfaRelayContext<Relay> {
    type Error = OfaErrorContext<Relay::Error>;
}

impl<Relay: OfaRelay> RuntimeContext for OfaRelayContext<Relay> {
    type Runtime = OfaRuntimeContext<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }
}

impl<Relay: OfaRelay> IbcPacket<OfaChainContext<Relay::SrcChain>, OfaChainContext<Relay::DstChain>>
    for OfaPacket<Relay>
{
    fn source_port(&self) -> &<Relay::SrcChain as OfaChain>::PortId {
        Relay::packet_src_port(&self.packet)
    }

    fn source_channel_id(&self) -> &<Relay::SrcChain as OfaChain>::ChannelId {
        Relay::packet_src_channel_id(&self.packet)
    }

    fn destination_port(&self) -> &<Relay::DstChain as OfaChain>::PortId {
        Relay::packet_dst_port(&self.packet)
    }

    fn destination_channel_id(&self) -> &<Relay::DstChain as OfaChain>::ChannelId {
        Relay::packet_dst_channel_id(&self.packet)
    }

    fn sequence(&self) -> &<Relay::SrcChain as OfaChain>::Sequence {
        Relay::packet_sequence(&self.packet)
    }

    fn timeout_height(&self) -> Option<&<Relay::DstChain as OfaChain>::Height> {
        Relay::packet_timeout_height(&self.packet)
    }

    fn timeout_timestamp(&self) -> &<Relay::DstChain as OfaChain>::Timestamp {
        Relay::packet_timeout_timestamp(&self.packet)
    }
}
