/*!
   Trait definition for [`HasEventType`].
*/

use crate::core::traits::sync::Async;

/**
   This is used for the chain context and the transaction context to declare
   that they have a unique `Self::Event` type, which corresponds to the
   events that are emitted from a transaction being committed to a chain.

   We define this as a separate trait so that we can use it in both a chain
   context and also a transaction context. Note that because a concrete context
   may implement both chain and transaction context at the same time,
   we want to avoid defining multiple associated `Event` types so that
   they can never be ambiguous.
*/
pub trait HasEventType: Async {
    /**
       The events that are emitted from a transaction being committed to a
       blockchain.

       The event type can be either dynamic typed, like `AbciEvent`, or static
       typed, like `IbcEvent`. The abstract type here do not inform of which
       specific variants an event may have. This is because the on-wire event
       format is essentially dynamic, and it is up to chain implementations to
       decide which events to emit and which formats the emitted events should
       have.

       In order to make the relayer framework general enough to support
       non-Cosmos chains, we also cannot make assumption on what events a chain
       may emit. By keeping the event type abstract, we can allow non-Cosmos
       chains to define custom components that process the events in different
       ways, and still allow them to reuse the other components in the relayer
       framework that do not interact with the event variants.

       Using dependency injection, we can impose additional constraints on what
       properties the `Event` type should have at the use site. An example use
       of this is the [`HasIbcEvent`](crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent)
       trait, which contains the IBC event variant types like
       [`WriteAcknowledgementEvent`](crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent::WriteAcknowledgementEvent),
       and _extraction_ methods to parse the variant information from the event.
    */
    type Event: Async;
}
