/*!
   Trait definitions for [`CanSendMessages`] and [`MessageSender`].
*/

use async_trait::async_trait;

use crate::chain::traits::types::event::HasEventType;
use crate::chain::traits::types::message::HasMessageType;
use crate::core::traits::sync::Async;
use crate::std_prelude::*;

/**
   This is a simplified interface offered by a chain context or a transaction
   context for atomically sending a list of [messages](HasMessageType::Message)
   to a chain.

   Behind the scene, the chain context may implement this by encoding the
   given messages into a transaction, and then sending it to the chain.

   Before the given messages are submitted as a transaction, the chain context
   may also perform additional operations, such as batching messages sent from
   other tasks into the same transaction.

   A chain context may also use other strategies of submitting messages. For
   example, a mock chain context can provide a mock implementation of sending
   messages, without mocking the part for submitting the messages as
   transactions.

    The implementation of [`send_messages`](Self::send_messages) _must_ treat
    the sending of messages as an atomic operation. i.e. the messages must all
    sent successfully, or all failed.

    In case if the total size of a given list of messages exceed some underlying
    transaction limit, the implementation _must not_ attempt to split the given
    messages into multiple transactions. This is because doing so could cause
    partial failure, which violates the atomicity constraint. Instead, the
    chain implementation should return an error and leave the task of splitting
    the messages to smaller batch to the caller.

    For example, the
    [`MaxTxSizeExceededError`](crate::transaction::impls::encoders::max_tx_size::MaxTxSizeExceededError)
    error is returned from the
    [`CheckEncodedTxSize`](crate::transaction::impls::encoders::max_tx_size::CheckEncodedTxSize)
    component if the total message size exceeds a given transaction size limit.
    A component like
    [`CanSpawnBatchMessageWorker`](crate::full::batch::worker::CanSpawnBatchMessageWorker)
    can then try and match against the error, and split the sent messages into
    smaller batches.

   This trait is automatically implemented by
   [`OfaChainWrapper`](crate::one_for_all::types::chain::OfaChainWrapper)
   for a chain context that implements
   [`OfaBaseChain`](crate::one_for_all::traits::chain::OfaBaseChain).
   From there, the [`CanSendMessages::send_messages`] method is derived from
   [`OfaBaseChain::send_messages`](crate::one_for_all::traits::chain::OfaBaseChain::send_messages).

   Additionally, this trait is also automatically implemented by
   [`OfaTxWrapper`](crate::one_for_all::types::transaction::OfaTxWrapper)
   for a chain context that implements
   [`OfaTxContext`](crate::one_for_all::traits::transaction::OfaTxContext).
   From there, the
   [`SendMessagesAsTx`](crate::transaction::impls::message_sender::SendMessagesAsTx)
   component is used to submit the messages as transaction using the transaction
   context. In other words, both the chain context and the transaction context
   provides the same interface for sending messages using this trait.
*/
#[async_trait]
pub trait CanSendMessages: HasMessageType + HasEventType {
    /**
        Given a list of [messages](HasMessageType::Message), submit the messages
        atomically to the chain.

        On success, the method returns a _nested_ list of
        [events](HasEventType::Event). The length of the outer list must match
        the length of the input message list. Each list of events in the
        outer list corresponds to the events emitted from processing the message
        at the same position in the input message list.

        On failure, the method returns an
        [error](crate::core::traits::error::HasErrorType::Error).
        Note that since the message sending must be atomic, the sending of
        messages must either all succeed or all failed. i.e. partial failure
        is forbidden.
    */
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;
}

/**
   The provider trait for [`CanSendMessages`].
*/
#[async_trait]
pub trait MessageSender<Chain>: Async
where
    Chain: HasMessageType + HasEventType,
{
    /**
       Corresponds to [`CanSendMessages::send_messages`]
    */
    async fn send_messages(
        chain: &Chain,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error>;
}
