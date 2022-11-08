/*!
   The traits containing the core abstract types for the chain context.

   A chain context is expected to implement at minimum the traits that
   are defined in this module.
*/

use crate::base::core::traits::error::HasError;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

/**
   This is used for the chain context and the transaction context to declare
   that they have a unique `Self::Message` type, which corresponds to messages
   that are submitted to a chain inside a transaction.

   We define this as a separate trait so that we can use it in both a chain
   context and also a transaction context. Note that because a concrete context
   may implement both chain and transaction context at the same time,
   we want to avoid defining multiple associated `Message` types so that
   they can never be ambiguous.
*/
pub trait HasMessageType: Async {
    type Message: Async;
}

/**
   This is used for the chain context and the transaction context to declare
   that they have a unique `Self::Event` type, which corresponds to the
   events that are generated from a transaction being committed to a chain.

   We define this as a separate trait so that we can use it in both a chain
   context and also a transaction context. Note that because a concrete context
   may implement both chain and transaction context at the same time,
   we want to avoid defining multiple associated `Event` types so that
   they can never be ambiguous.
*/
pub trait HasEventType: Async {
    type Event: Async;
}

/**
   This covers the minimal abstract types that are used inside a chain context.

   A chain context should have the following abstract types:

   -   [`Error`](HasError::Error) - the error type encapsulating errors occured
       during chain operations.

   -   [`Height`](Self::Height) - the height of a chain, which should behave like
       natural numbers.

   -   [`Timestamp`](Self::Timestamp) - the timestamp of a chain, which should
       increment monotonically.

   -   [`Message`](HasMessageType::Message) - the messages being submitted
       to a chain.

   -   [`Event`](HasEventType::Event) - the events that are generated after
       a transaction is committed to a chain.
*/
pub trait HasChainTypes: HasMessageType + HasEventType + HasError {
    type Height: Ord + Async;

    type Timestamp: Ord + Async;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;
}

/// The datatypes that IBC chains need to expose in addition to the datatypes
/// exposed by the base `ChainContext`.
///
/// Each [`HasIbcChainTypes`] is parameterized by a `Counterparty` chain
/// which must also implement the `ChainContext` trait.
pub trait HasIbcChainTypes<Counterparty>: HasChainTypes
where
    Counterparty: HasChainTypes,
{
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;
}
