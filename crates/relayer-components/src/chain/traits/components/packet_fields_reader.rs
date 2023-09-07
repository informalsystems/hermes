use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::component::{DelegateComponent, HasComponents};

pub struct PacketFieldsReaderComponent;

pub trait PacketFieldsReader<Chain, Counterparty>
where
    Chain: HasIbcPacketTypes<Counterparty> + HasIbcChainTypes<Counterparty>,
    Counterparty: HasIbcChainTypes<Chain>,
{
    fn incoming_packet_src_channel_id(packet: &Chain::IncomingPacket) -> &Counterparty::ChannelId;

    fn incoming_packet_dst_channel_id(packet: &Chain::IncomingPacket) -> &Chain::ChannelId;

    fn incoming_packet_src_port(packet: &Chain::IncomingPacket) -> &Counterparty::PortId;

    fn incoming_packet_dst_port(packet: &Chain::IncomingPacket) -> &Chain::PortId;

    fn incoming_packet_sequence(packet: &Chain::IncomingPacket) -> &Counterparty::Sequence;

    fn incoming_packet_timeout_height(packet: &Chain::IncomingPacket) -> Option<&Chain::Height>;

    fn incoming_packet_timeout_timestamp(packet: &Chain::IncomingPacket) -> &Chain::Timestamp;

    fn outgoing_packet_src_channel_id(packet: &Chain::OutgoingPacket) -> &Chain::ChannelId;

    fn outgoing_packet_dst_channel_id(packet: &Chain::OutgoingPacket) -> &Counterparty::ChannelId;

    fn outgoing_packet_src_port(packet: &Chain::OutgoingPacket) -> &Chain::PortId;

    fn outgoing_packet_dst_port(packet: &Chain::OutgoingPacket) -> &Counterparty::PortId;

    fn outgoing_packet_sequence(packet: &Chain::OutgoingPacket) -> &Chain::Sequence;

    fn outgoing_packet_timeout_height(
        packet: &Chain::OutgoingPacket,
    ) -> Option<&Counterparty::Height>;

    fn outgoing_packet_timeout_timestamp(
        packet: &Chain::OutgoingPacket,
    ) -> &Counterparty::Timestamp;
}

pub trait CanReadPacketFields<Counterparty>:
    HasIbcPacketTypes<Counterparty> + HasIbcChainTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    fn incoming_packet_src_channel_id(packet: &Self::IncomingPacket) -> &Counterparty::ChannelId;

    fn incoming_packet_dst_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId;

    fn incoming_packet_src_port(packet: &Self::IncomingPacket) -> &Counterparty::PortId;

    fn incoming_packet_dst_port(packet: &Self::IncomingPacket) -> &Self::PortId;

    fn incoming_packet_sequence(packet: &Self::IncomingPacket) -> &Counterparty::Sequence;

    fn incoming_packet_timeout_height(packet: &Self::IncomingPacket) -> Option<&Self::Height>;

    fn incoming_packet_timeout_timestamp(packet: &Self::IncomingPacket) -> &Self::Timestamp;

    fn outgoing_packet_src_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId;

    fn outgoing_packet_dst_channel_id(packet: &Self::OutgoingPacket) -> &Counterparty::ChannelId;

    fn outgoing_packet_src_port(packet: &Self::OutgoingPacket) -> &Self::PortId;

    fn outgoing_packet_dst_port(packet: &Self::OutgoingPacket) -> &Counterparty::PortId;

    fn outgoing_packet_sequence(packet: &Self::OutgoingPacket) -> &Self::Sequence;

    fn outgoing_packet_timeout_height(
        packet: &Self::OutgoingPacket,
    ) -> Option<&Counterparty::Height>;

    fn outgoing_packet_timeout_timestamp(packet: &Self::OutgoingPacket)
        -> &Counterparty::Timestamp;
}

impl<Component, Chain, Counterparty> PacketFieldsReader<Chain, Counterparty> for Component
where
    Chain: HasIbcPacketTypes<Counterparty> + HasIbcChainTypes<Counterparty>,
    Counterparty: HasIbcChainTypes<Chain>,
    Component: DelegateComponent<PacketFieldsReaderComponent>,
    Component::Delegate: PacketFieldsReader<Chain, Counterparty>,
{
    fn incoming_packet_src_channel_id(packet: &Chain::IncomingPacket) -> &Counterparty::ChannelId {
        Component::Delegate::incoming_packet_src_channel_id(packet)
    }

    fn incoming_packet_dst_channel_id(packet: &Chain::IncomingPacket) -> &Chain::ChannelId {
        Component::Delegate::incoming_packet_dst_channel_id(packet)
    }

    fn incoming_packet_src_port(packet: &Chain::IncomingPacket) -> &Counterparty::PortId {
        Component::Delegate::incoming_packet_src_port(packet)
    }

    fn incoming_packet_dst_port(packet: &Chain::IncomingPacket) -> &Chain::PortId {
        Component::Delegate::incoming_packet_dst_port(packet)
    }

    fn incoming_packet_sequence(packet: &Chain::IncomingPacket) -> &Counterparty::Sequence {
        Component::Delegate::incoming_packet_sequence(packet)
    }

    fn incoming_packet_timeout_height(packet: &Chain::IncomingPacket) -> Option<&Chain::Height> {
        Component::Delegate::incoming_packet_timeout_height(packet)
    }

    fn incoming_packet_timeout_timestamp(packet: &Chain::IncomingPacket) -> &Chain::Timestamp {
        Component::Delegate::incoming_packet_timeout_timestamp(packet)
    }

    fn outgoing_packet_src_channel_id(packet: &Chain::OutgoingPacket) -> &Chain::ChannelId {
        Component::Delegate::outgoing_packet_src_channel_id(packet)
    }

    fn outgoing_packet_dst_channel_id(packet: &Chain::OutgoingPacket) -> &Counterparty::ChannelId {
        Component::Delegate::outgoing_packet_dst_channel_id(packet)
    }

    fn outgoing_packet_src_port(packet: &Chain::OutgoingPacket) -> &Chain::PortId {
        Component::Delegate::outgoing_packet_src_port(packet)
    }

    fn outgoing_packet_dst_port(packet: &Chain::OutgoingPacket) -> &Counterparty::PortId {
        Component::Delegate::outgoing_packet_dst_port(packet)
    }

    fn outgoing_packet_sequence(packet: &Chain::OutgoingPacket) -> &Chain::Sequence {
        Component::Delegate::outgoing_packet_sequence(packet)
    }

    fn outgoing_packet_timeout_height(
        packet: &Chain::OutgoingPacket,
    ) -> Option<&Counterparty::Height> {
        Component::Delegate::outgoing_packet_timeout_height(packet)
    }

    fn outgoing_packet_timeout_timestamp(
        packet: &Chain::OutgoingPacket,
    ) -> &Counterparty::Timestamp {
        Component::Delegate::outgoing_packet_timeout_timestamp(packet)
    }
}

impl<Chain, Counterparty> CanReadPacketFields<Counterparty> for Chain
where
    Chain: HasIbcPacketTypes<Counterparty> + HasIbcChainTypes<Counterparty> + HasComponents,
    Counterparty: HasIbcChainTypes<Chain>,
    Chain::Components: PacketFieldsReader<Chain, Counterparty>,
{
    fn incoming_packet_src_channel_id(packet: &Chain::IncomingPacket) -> &Counterparty::ChannelId {
        Chain::Components::incoming_packet_src_channel_id(packet)
    }

    fn incoming_packet_dst_channel_id(packet: &Chain::IncomingPacket) -> &Chain::ChannelId {
        Chain::Components::incoming_packet_dst_channel_id(packet)
    }

    fn incoming_packet_src_port(packet: &Chain::IncomingPacket) -> &Counterparty::PortId {
        Chain::Components::incoming_packet_src_port(packet)
    }

    fn incoming_packet_dst_port(packet: &Chain::IncomingPacket) -> &Chain::PortId {
        Chain::Components::incoming_packet_dst_port(packet)
    }

    fn incoming_packet_sequence(packet: &Chain::IncomingPacket) -> &Counterparty::Sequence {
        Chain::Components::incoming_packet_sequence(packet)
    }

    fn incoming_packet_timeout_height(packet: &Chain::IncomingPacket) -> Option<&Chain::Height> {
        Chain::Components::incoming_packet_timeout_height(packet)
    }

    fn incoming_packet_timeout_timestamp(packet: &Chain::IncomingPacket) -> &Chain::Timestamp {
        Chain::Components::incoming_packet_timeout_timestamp(packet)
    }

    fn outgoing_packet_src_channel_id(packet: &Chain::OutgoingPacket) -> &Chain::ChannelId {
        Chain::Components::outgoing_packet_src_channel_id(packet)
    }

    fn outgoing_packet_dst_channel_id(packet: &Chain::OutgoingPacket) -> &Counterparty::ChannelId {
        Chain::Components::outgoing_packet_dst_channel_id(packet)
    }

    fn outgoing_packet_src_port(packet: &Chain::OutgoingPacket) -> &Chain::PortId {
        Chain::Components::outgoing_packet_src_port(packet)
    }

    fn outgoing_packet_dst_port(packet: &Chain::OutgoingPacket) -> &Counterparty::PortId {
        Chain::Components::outgoing_packet_dst_port(packet)
    }

    fn outgoing_packet_sequence(packet: &Chain::OutgoingPacket) -> &Chain::Sequence {
        Chain::Components::outgoing_packet_sequence(packet)
    }

    fn outgoing_packet_timeout_height(
        packet: &Chain::OutgoingPacket,
    ) -> Option<&Counterparty::Height> {
        Chain::Components::outgoing_packet_timeout_height(packet)
    }

    fn outgoing_packet_timeout_timestamp(
        packet: &Chain::OutgoingPacket,
    ) -> &Counterparty::Timestamp {
        Chain::Components::outgoing_packet_timeout_timestamp(packet)
    }
}
