use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::chain::traits::message_sender::CanSendMessages;
use crate::base::chain::traits::types::{HasChainTypes, HasEventType, HasMessageType};
use crate::base::core::traits::error::HasError;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

/**
   A wrapper type that wraps a relay context with a target into a chain context.

   This allows the relay context to be used on components that require a chain context.
   The main use case is to wrap the relay context to implement [`CanSendMessages`].

   The relay context on its own can implement
   [`CanSendIbcMessages`](crate::base::relay::traits::ibc_message_sender::CanSendIbcMessages)
   but not [`CanSendMessages`], as the former is parameterized by a relay target.
   The two traits also have different charasteristics, as `CanSendIbcMessages` allows
   middleware components such as
   [`SendIbcMessagesWithUpdateClient`](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
   to access the relay context and build `UpdateClient` messages to append to the
   front of incoming messages. On the other hand, [`CanSendMessages`] can only
   access the chain context but not the counterparty chain context, thus not able
   to build `UpdateClient` messages in the middle of the pipeline.

   With the `RelayToChain` wrapper, this allows the relay context to pretend that it
   is a chain context while also holding the counterparty chain context. The wrapper
   allows the relay context to be used with components that need to be polymorphic
   over any context that supports sending of messages, such as the
   [batch worker component](crate::full::batch).
*/

pub struct RelayToChain<Relay, Target> {
    pub relay: Relay,
    pub phantom: PhantomData<Target>,
}

impl<Relay, Target> HasError for RelayToChain<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    type Error = Relay::Error;
}

impl<Relay, Target> HasMessageType for RelayToChain<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    type Message = <Target::TargetChain as HasMessageType>::Message;
}

impl<Relay, Target> HasEventType for RelayToChain<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    type Event = <Target::TargetChain as HasEventType>::Event;
}

impl<Relay, Target> HasChainTypes for RelayToChain<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    type Height = <Target::TargetChain as HasChainTypes>::Height;

    type Timestamp = <Target::TargetChain as HasChainTypes>::Timestamp;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Target::TargetChain::estimate_message_len(message)
    }
}

#[async_trait]
impl<Relay, Target> CanSendMessages for RelayToChain<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: CanSendMessages,
{
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        Target::target_chain(&self.relay)
            .send_messages(messages)
            .await
    }
}
