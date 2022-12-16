use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

/**
   The abstract types for a chain context when it is used for IBC
   communication with a `Counterparty` chain context.

   In contrast to [`HasChainTypes`], this trait is parameterized by a
   `Counterparty` chain context, which is also required to implement
   [`HasChainTypes`].

   Because of the `Counterparty` parameter, the associated types
   in this trait are going to be different when used with different
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
   _not_ expected to have access to resources on the counterparty chain. That
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
