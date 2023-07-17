/*!
   Trait definitions for [`HasWriteAcknowledgementEvent`].
*/

use crate::chain::traits::types::event::HasEventType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::sync::Async;

/**
   Indicates that a chain context's
   [`Event`](crate::chain::traits::types::event::HasEventType::Event)
   type contains a [`WriteAcknowledgementEvent`](Self::WriteAcknowledgementEvent) variant.
*/
pub trait HasWriteAcknowledgementEvent<Counterparty>: HasEventType {
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
       Try to extract an abstract
       [`Event`](crate::chain::traits::types::event::HasEventType::Event)
       type into a
       [`WriteAcknowledgementEvent`](Self::WriteAcknowledgementEvent).
       If the extraction fails, return `None`.

       Since an event type may contain many variants, it is not guaranteed
       that the event extraction would be successful. If the concrete
       `Event` is dynamic-typed, then the extraction may also fail due to
       parse errors.
    */
    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;
}

pub trait CanBuildPacketFromWriteAckEvent<Counterparty>:
    HasWriteAcknowledgementEvent<Counterparty> + HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    /**
       Extract the [`IncomingPacket`](HasIbcPacketTypes::IncomingPacket)
       from a write acknowledgement event.

       Since write acknowledgements are emitted from a destination chain (self),
       it is necessary for the event to correspond to an incoming packet
       (with self being the destination).

       Here we assume that a write acknowledgement event always contains
       the packet data. This is currently true for Cosmos chains. However
       in case additional queries are required, then this method should be
       refactored into a method like
       `query_packet_from_write_acknowledgement_event`.
    */
    fn build_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket;
}
