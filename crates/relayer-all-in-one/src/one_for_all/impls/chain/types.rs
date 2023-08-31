use ibc_relayer_components::chain::traits::types::chain_id::{HasChainId, HasChainIdType};
use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::height::{CanIncrementHeight, HasHeightType};
use ibc_relayer_components::chain::traits::types::ibc::{
    HasCounterpartyMessageHeight, HasIbcChainTypes,
};
use ibc_relayer_components::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::{
    CanBuildPacketFromWriteAckEvent, HasWriteAcknowledgementEvent,
};
use ibc_relayer_components::chain::traits::types::message::{
    CanEstimateMessageSize, HasMessageType,
};
use ibc_relayer_components::chain::traits::types::packet::{HasIbcPacketFields, HasIbcPacketTypes};
use ibc_relayer_components::chain::traits::types::timestamp::HasTimestampType;
use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components_extra::components::extra::chain::ExtraChainComponents;

use crate::one_for_all::traits::chain::{OfaChain, OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::std_prelude::*;

impl<Chain, Name> DelegateComponent<Name> for OfaChainWrapper<Chain>
where
    Chain: Async,
{
    type Delegate = ExtraChainComponents<OfaComponents>;
}

impl<Chain: OfaChain> HasRuntime for OfaChainWrapper<Chain> {
    type Runtime = Chain::Runtime;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Chain::Error {
        Chain::runtime_error(e)
    }
}

impl<Chain: OfaChainTypes> HasMessageType for OfaChainWrapper<Chain> {
    type Message = Chain::Message;
}

impl<Chain: OfaChain> CanEstimateMessageSize for OfaChainWrapper<Chain> {
    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_size(message)
    }
}

impl<Chain: OfaChainTypes> HasEventType for OfaChainWrapper<Chain> {
    type Event = Chain::Event;
}

impl<Chain: OfaChainTypes> HasHeightType for OfaChainWrapper<Chain> {
    type Height = Chain::Height;
}

impl<Chain: OfaChain> CanIncrementHeight for OfaChainWrapper<Chain> {
    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error> {
        Chain::increment_height(height)
    }
}

impl<Chain: OfaChainTypes> HasChainIdType for OfaChainWrapper<Chain> {
    type ChainId = Chain::ChainId;
}

impl<Chain: OfaChainTypes> HasTimestampType for OfaChainWrapper<Chain> {
    type Timestamp = Chain::Timestamp;
}

impl<Chain: OfaChain> HasChainId for OfaChainWrapper<Chain> {
    fn chain_id(&self) -> &Self::ChainId {
        self.chain.chain_id()
    }
}

impl<Chain, Counterparty> HasIbcChainTypes<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;
}

impl<Chain, Counterparty> HasCounterpartyMessageHeight<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    fn counterparty_message_height_for_update_client(
        message: &Self::Message,
    ) -> Option<Counterparty::Height> {
        Chain::counterparty_message_height_for_update_client(message)
    }
}

impl<Chain, Counterparty> HasIbcPacketTypes<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type IncomingPacket = Chain::IncomingPacket;

    type OutgoingPacket = Chain::OutgoingPacket;
}

impl<Chain, Counterparty> HasIbcPacketFields<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
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
    Counterparty: OfaChainTypes,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        Chain::try_extract_write_acknowledgement_event(event)
    }
}

impl<Chain, Counterparty> CanBuildPacketFromWriteAckEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    fn build_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket {
        Chain::extract_packet_from_write_acknowledgement_event(ack)
    }
}

impl<Chain, Counterparty> HasSendPacketEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
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
