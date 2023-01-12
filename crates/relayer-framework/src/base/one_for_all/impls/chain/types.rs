use crate::base::chain::traits::ibc_event::{HasSendPacketEvent, HasWriteAcknowledgementEvent};
use crate::base::chain::traits::types::height::HasHeightType;
use crate::base::chain::traits::types::{
    CanEstimateMessageSize, HasChainTypes, HasEventType, HasIbcChainTypes, HasIbcPacketTypes,
    HasMessageType,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;

impl<Chain: OfaBaseChain> HasErrorType for OfaChainWrapper<Chain> {
    type Error = Chain::Error;
}

impl<Chain: OfaBaseChain> HasRuntime for OfaChainWrapper<Chain> {
    type Runtime = OfaRuntimeWrapper<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Chain::Error {
        Chain::runtime_error(e)
    }
}

impl<Chain: OfaBaseChain> HasMessageType for OfaChainWrapper<Chain> {
    type Message = Chain::Message;
}

impl<Chain: OfaBaseChain> CanEstimateMessageSize for OfaChainWrapper<Chain> {
    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_size(message)
    }
}

impl<Chain: OfaBaseChain> HasEventType for OfaChainWrapper<Chain> {
    type Event = Chain::Event;
}

impl<Chain: OfaBaseChain> HasHeightType for OfaChainWrapper<Chain> {
    type Height = Chain::Height;
}

impl<Chain: OfaBaseChain> HasChainTypes for OfaChainWrapper<Chain> {
    type Timestamp = Chain::Timestamp;
}

impl<Chain, Counterparty> HasIbcChainTypes<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height> {
        Chain::counterparty_message_height(message)
    }
}

impl<Chain, Counterparty> HasIbcPacketTypes<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type IncomingPacket = Chain::IncomingPacket;

    type OutgoingPacket = Chain::OutgoingPacket;

    fn incoming_packet_src_channel_id(packet: &Self::IncomingPacket) -> &Counterparty::ChannelId {
        Chain::incoming_packet_src_channel_id(packet)
    }

    fn incoming_packet_dst_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId {
        Chain::incoming_packet_dst_channel_id(packet)
    }

    fn incoming_packet_src_port(packet: &Self::IncomingPacket) -> &Counterparty::PortId {
        Chain::incoming_packet_src_port(packet)
    }

    fn incoming_packet_dst_port(packet: &Self::IncomingPacket) -> &Self::PortId {
        Chain::incoming_packet_dst_port(packet)
    }

    fn incoming_packet_sequence(packet: &Self::IncomingPacket) -> &Counterparty::Sequence {
        Chain::incoming_packet_sequence(packet)
    }

    fn incoming_packet_timeout_height(packet: &Self::IncomingPacket) -> Option<&Self::Height> {
        Chain::incoming_packet_timeout_height(packet)
    }

    fn incoming_packet_timeout_timestamp(packet: &Self::IncomingPacket) -> &Self::Timestamp {
        Chain::incoming_packet_timeout_timestamp(packet)
    }

    fn outgoing_packet_src_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId {
        Chain::outgoing_packet_src_channel_id(packet)
    }

    fn outgoing_packet_dst_channel_id(packet: &Self::OutgoingPacket) -> &Counterparty::ChannelId {
        Chain::outgoing_packet_dst_channel_id(packet)
    }

    fn outgoing_packet_src_port(packet: &Self::OutgoingPacket) -> &Self::PortId {
        Chain::outgoing_packet_src_port(packet)
    }

    fn outgoing_packet_dst_port(packet: &Self::OutgoingPacket) -> &Counterparty::PortId {
        Chain::outgoing_packet_dst_port(packet)
    }

    fn outgoing_packet_sequence(packet: &Self::OutgoingPacket) -> &Self::Sequence {
        Chain::outgoing_packet_sequence(packet)
    }

    fn outgoing_packet_timeout_height(
        packet: &Self::OutgoingPacket,
    ) -> Option<&Counterparty::Height> {
        Chain::outgoing_packet_timeout_height(packet)
    }

    fn outgoing_packet_timeout_timestamp(
        packet: &Self::OutgoingPacket,
    ) -> &Counterparty::Timestamp {
        Chain::outgoing_packet_timeout_timestamp(packet)
    }
}

impl<Chain, Counterparty> HasWriteAcknowledgementEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        Chain::try_extract_write_acknowledgement_event(event)
    }
}

impl<Chain, Counterparty> HasSendPacketEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type SendPacketEvent = Chain::SendPacketEvent;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent> {
        Chain::try_extract_send_packet_event(event)
    }

    fn extract_packet_from_send_packet_event(
        event: &Self::SendPacketEvent,
    ) -> Self::OutgoingPacket {
        Chain::extract_packet_from_send_packet_event(event)
    }
}
