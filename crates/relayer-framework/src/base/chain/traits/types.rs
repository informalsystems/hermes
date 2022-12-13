/*!
   The traits containing the core abstract types for the chain context.

   A chain context is expected to implement at minimum the traits that
   are defined in this module.
*/

use crate::base::core::traits::error::HasErrorType;
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
pub trait HasMessageType: HasErrorType {
    /**
       The messages that can be assembled into transactions and be submitted to
       a blockchain.

       The message type can be either dynamic typed, like `Any`, or static typed,
       like `Ics26Envelope`. Either way, it is treated as an opaque type by the
       relayer framework, so that this can be used for sending messages to
       non-Cosmos chains as well. It is worth noting that depending on the
       concrete chain, it may be _not necessary_ to support protobufs for the
       `Message` type.

       Unlike the current message type in the original relayer, if the `Message`
       type is used in a transaction context, it is _required_
       that the `Message` type here to support _late binding_ of the signer field.
       In other words, the chain context is required to be able to construct
       messages without providing a signer, and then only provide a signer when
       assembling the messages into transactions.

       The late binding of the signer field is necessary to make it possible
       for the relayer framework to multiplex the submission of transactions
       using multiple wallets. Depending on the number of messages being sent
       at a given time frame, a message may be assigned with different signers
       when being assembled into transactions.

       The relayer framework delegates the _construction_ of messages to
       specialized traits such as
       [`CanBuildUpdateClientMessage`](crate::base::relay::traits::messages::update_client::CanBuildUpdateClientMessage).
       Because the construction of messages typically also requires querying
       from the chain, the relayer framework lets the concrete chain contexts
       to perform both the querying operations and message construction
       operations at once. As a result, there is rarely a need for the relayer
       framework to know about specific message variants, such as
       `UpdateCientMesssage`.

       The relayer framework currently requires two operations to be supported
       by the abstract `Message` type:
       [`estimate_message_len`](Self::estimate_message_len) and
       [`counterparty_message_height`](HasIbcChainTypes::counterparty_message_height).
    */
    type Message: Async;

    /**
       Estimate the size of a message after it is encoded into raw bytes
       inside a transaction.

       Because the signer field of a message is late-bound, it may not
       be possible to get a precise size if the signer field can have
       dynamic length. For the purpose of length estimation, the concrete
       context may replace the message's signer field with a dummy signer
       value, so that it can be encoded into raw bytes.

       This is mainly used by
       [`BatchMessageWorker`](crate::full::batch::worker::BatchMessageWorker)
       to estimate the messages size when batching messages. We may consider
       moving this method into a separate crate if it is not being used
       elsewhere.
    */
    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;
}

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
       of this is the [`HasIbcEvent`](crate::base::chain::traits::ibc_event::HasIbcEvents)
       trait, which contains the IBC event variant types like
       [`WriteAcknowledgementEvent`](crate::base::chain::traits::ibc_event::HasIbcEvents::WriteAcknowledgementEvent),
       and _extraction_ methods to parse the variant information from the event.
    */
    type Event: Async;
}

/**
   This covers the minimal abstract types that are used inside a chain context.

   A chain context have the following abstract types:

   -   [`Error`](HasErrorType::Error) - the error type encapsulating errors occured
       during chain operations.

   -   [`Height`](Self::Height) - the height of a chain, which should behave like
       natural numbers.

   -   [`Timestamp`](Self::Timestamp) - the timestamp of a chain, which should
       increment monotonically.

   -   [`Message`](HasMessageType::Message) - the messages being submitted
       to a chain.

   -   [`Event`](HasEventType::Event) - the events that are emitted after
       a transaction is committed to a chain.

    This trait only covers chain types that involve a single chain. For IBC
    chain types that involve _two_ chains, the abstract types are defined
    in [`HasIbcChainTypes`].

    Notice that a chain context do not contain a `Transaction` abstract
    type. This is because we separate the concerns of normal chain operations
    from the special concerns of assembling chain messages into transactions
    and broadcasting it to the blockchain. See the
    [`transaction`](crate::base::transaction) module for more information
    about the transaction context.
*/
pub trait HasChainTypes: HasMessageType + HasEventType + HasErrorType {
    /**
       The height of the chain, which should behave like natural numbers.

       By default, the height only contains the `Ord` constraint, and does
       not support operations like addition.

       We can impose additional constraints at the use site of `HasChainTypes`.
       However doing so may impose limitations on which concrete types
       the `Height` type can be.

       By keeping the abstract type minimal, we can for example use
       `u8` or `u128` as the `Height` type during testing, and use the
       more complex Cosmos height type during production.
    */
    type Height: Ord + Async;

    /**
       The timestamp of a chain, which should increment monotonically.

       By default, the timestamp only contains the `Ord` constraint, and does
       not support operations like adding to a `Duration`.

       We can impose additional constraints at the use site of `HasChainTypes`.
       However doing so may impose limitations on which concrete types
       the `Timestamp` type can be.

       By keeping the abstract type minimal, we can for example use
       simple `u8` or `u128` in seconds as the `Timestamp` type during testing,
       and use the more complex types like `DateTime` type during production.

       This especially helps given that having a canonical time type is
       still largely an unsolved problem in software engineering. Depending
       on the specific use cases, different concrete contexts may want to
       use different date time types to enforce certain invariants.
       By keeping this type abstract, we provide the flexibility to
       concrete context implementers to decide which exact time type
       they would like to use.
    */
    type Timestamp: Ord + Async;
}

/**
   The abstract types for a chain context, when it is used for IBC
   communication wit a `Counterparty` chain context.

   In contrast to [`HasChainTypes`], this trait is parameterized by a
   `Counterparty` chain context, which is also required to implement
   [`HasChainTypes`].

   Because of the `Counterparty` parameter, the associated types
   in this trait is going to be different when used with different
   counterparty chain contexts. In other words, the type
   `<ChainA as HasIbcChainTypes<ChainB>>::ClientId` is different from
   `<ChainA as HasIbcChainTypes<ChainC>>::ClientId` if `ChainB` and `ChainC`
   are different.

   This is intentional, as we want to distinguish IBC identifiers associated
   with different chains and avoid accidentally mixing them up. This is
   particularly useful when implementing the relayer, because we cannot
   for example accidentally use a `ChannelId` from `SrcChain` to `DstChain`
   as a `ChannelId` from `DstChain` to `SrcChain`.

   Having the IBC chain types parameterized on the counterparty chain also
   allows a chain context to decide on different concrete types depending
   on which counterparty chain it is. For example, a Cosmos chain context
   connected with a non-Cosmos chain context may want to use different
   `ClientId` type, as compared to connecting to a Cosmos chain.

   Note that even when a chain context implements `HasIbcChainTypes`, it is
   _not_ expected to has access to resources on the counterparty chain. That
   would require access to the counterparty chain context, which is implemented
   separately from the self chain context. Instead, operations that require
   access to two chain contexts are handled by the
   [relay context](crate::base::relay).
*/
pub trait HasIbcChainTypes<Counterparty>: HasChainTypes
where
    Counterparty: HasChainTypes,
{
    /**
       The client ID of the counterparty chain, that is stored on the self
       chain.
    */
    type ClientId: Async;

    /**
       The connection ID of the counterparty chain, that is stored on the self
       chain.
    */
    type ConnectionId: Async;

    /**
       The channel ID of the counterparty chain, that is stored on the self
       chain.
    */
    type ChannelId: Async;

    /**
       The port ID of the counterparty chain, that is stored on the self
       chain.
    */
    type PortId: Async;

    /**
       The IBC packet sequence for the packet that is sent from the self chain
       to the counterparty chain.

       Note that for sequences of packets that are sent from the counterparty
       chain to self, the `Counterparty::Sequence` will be used.
    */
    type Sequence: Async;

    /**
       Get the height of the counterparty chain that an IBC message is based
       on when it is constructed to be sent to the self chain. If the message
       is not IBC-related, this would return `None`.

       This is used by the
       [`SendIbcMessagesWithUpdateClient`](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
       message sender middleware to attach `UpdateClient` messages to the
       front of the message batch before sending it to the downstream
       message sender.

       The way this works is as follows: recall that the relayer relays IBC
       packets by constructing messages from one chain and send it to
       the other chain. In this case, we have IBC events happening on
       the `Counterparty` chain, which the relayer would construct
       messages targetting this self chain. So any IBC message that the self
       chain received would correspond to events happening on the `Counterparty`
       chain. With this method, we are thus getting the
       [`Counterparty::Height`](HasChainTypes::Height) and _not_ `Self::Height`.
    */
    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;
}
