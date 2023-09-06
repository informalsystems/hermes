/*!
   Trait definition for [`HasIbcPacketTypes`].
*/

use crate::core::traits::sync::Async;

/**
    Contains the abstract packet types for a chain context to send and receive
    IBC packets from a counterparty chain.

    To enable IBC communication, a chain context needs to have _two_ packet
    types: [`IncomingPacket`](Self::IncomingPacket) for receiving packets
    sent from a counterparty chain to the self (given) chain, and
    [`OutgoingPacket`](Self::OutgoingPacket) for sending packets from the self
    chain to the counterparty chain.

    The two packet types are distinct, because the fields of the packets are
    different. For example, the
    [source channel ID](Self::incoming_packet_src_channel_id)
    of an incoming packet is the counterparty chain's channel ID, but the
    source channel ID of an outgoing packet is the self chain's channel ID.
    For each field in a packet, there is one accessor method for the incoming
    packet, and one for the outgoing packet.

    The trait [`HasIbcPacketTypes`] also requires the `Counterparty` chain
    context to implement [`HasIbcPacketTypes`], with `Self` being the
    counterparty of `Counterparty`. Additionally, there is a constraint that
    the `Counterparty`'s [`IncomingPacket`](Self::IncomingPacket) is the same
    as `Self`'s [`OutgoingPacket`](Self::OutgoingPacket), and that
    the `Counterparty`'s [`OutgoingPacket`](Self::OutgoingPacket) is the same
    as `Self`'s [`IncomingPacket`](Self::IncomingPacket). This ensures that
    there is no type mismatch when a chain's
    [`OutgoingPacket`](Self::OutgoingPacket) is sent to a counterparty chain,
    and when a chain receives [`IncomingPacket`](Self::IncomingPacket) that is
    coming from a counterparty chain.
*/
pub trait HasIbcPacketTypes<Counterparty>: Async {
    /**
       A packet sent from counterparty to self.

       - Packet source: `Counterparty`
       - Packet destination: `Self`
    */
    type IncomingPacket: Async;

    /**
       A packet sent from self to counterparty.

       - Packet source: `Self`
       - Packet destination: `Counterparty`
    */
    type OutgoingPacket: Async;
}
