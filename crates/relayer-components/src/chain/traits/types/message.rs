/*!
   Trait definitions for [`HasMessageType`] and [`CanEstimateMessageSize`].
*/

use core::fmt::Debug;

use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
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
       [`CanBuildUpdateClientMessage`](crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage).
       Because the construction of messages typically also requires querying
       from the chain, the relayer framework lets the concrete chain contexts
       to perform both the querying operations and message construction
       operations at once. As a result, there is rarely a need for the relayer
       framework to know about specific message variants, such as
       `UpdateCientMesssage`.
    */
    type Message: Async + Debug;
}

pub trait CanEstimateMessageSize: HasMessageType + HasErrorType {
    /**
       Estimate the size of a message after it is encoded into raw bytes
       inside a transaction.

       Because the signer field of a message is late-bound, it may not
       be possible to get a precise size if the signer field can have
       dynamic length. For the purpose of length estimation, the concrete
       context may replace the message's signer field with a dummy signer
       value, so that it can be encoded into raw bytes.

       This is mainly used by the `BatchMessageWorker` to estimate the
       the message size when batching messages. We may consider moving
       this method into a separate crate if it is not being used elsewhere.
    */
    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error>;
}
