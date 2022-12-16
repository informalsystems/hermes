use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::core::traits::sync::Async;

pub trait HasIbcPacketTypes<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    /*
       A packet sent from counterparty to self.

       - Packet source: `Counterparty`
       - Packet destination: `Self`
    */
    type IncomingPacket: Async;

    /*
       A packet sent from self to counterparty.

       - Packet source: `Self`
       - Packet destination: `Counterparty`
    */
    type OutgoingPacket: Async;

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
        packet: &Self::IncomingPacket,
    ) -> Option<&Counterparty::Height>;

    fn outgoing_packet_timeout_timestamp(packet: &Self::IncomingPacket)
        -> &Counterparty::Timestamp;
}
