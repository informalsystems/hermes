use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::base::core::traits::sync::Async;

/**
   Indicates that a chain context's
   [`Event`](crate::base::chain::traits::types::event::HasEventType::Event)
   type contains a [`SendPacketEvent`](Self::SendPacketEvent) variant.
*/
pub trait HasSendPacketEvent<Counterparty>: HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    type SendPacketEvent: Async;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent>;

    fn extract_packet_from_send_packet_event(event: &Self::SendPacketEvent)
        -> Self::OutgoingPacket;
}
