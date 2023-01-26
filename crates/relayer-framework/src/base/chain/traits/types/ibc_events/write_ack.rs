use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::base::core::traits::sync::Async;

/**
   Indicates that a chain context's
   [`Event`](crate::base::chain::traits::types::event::HasEventType::Event)
   type contains a [`WriteAcknowledgementEvent`](Self::WriteAcknowledgementEvent) variant.
*/
pub trait HasWriteAcknowledgementEvent<Counterparty>: HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    /**
       The write acknowledgement event that is emitted when a `RecvPacket`
       message is committed to a chain.

       At the moment, there is no need for the relayer framework to know
       further information about the write acknowledgement event, other
       than passing it down to the concrete context to build the `Ack`
       message.

       If new components have the need to extract information out of
       the write acknowledgement event, such as the ack payload,
       we can add new methods to this trait to do the extraction.
    */
    type WriteAcknowledgementEvent: Async;

    /**
       Try to convert an abstract
       [`Event`](crate::base::chain::traits::types::event::HasEventType::Event)
       type into a
       [`WriteAcknowledgementEvent`](Self::WriteAcknowledgementEvent).
       If the conversion fails, return `None`.

       Since an event type may contain many variants, it is not guaranteed
       that the event extraction would be successful. If the concrete
       `Event` is dynamic-typed, then the extraction may also fail due to
       parse errors.
    */
    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket;
}
