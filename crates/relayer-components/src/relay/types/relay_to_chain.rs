use core::marker::PhantomData;

use async_trait::async_trait;

use crate::chain::traits::components::message_sender::CanSendMessages;
use crate::chain::traits::types::chain_id::HasChainIdType;
use crate::chain::traits::types::event::HasEventType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::message::{CanEstimateMessageSize, HasMessageType};
use crate::chain::traits::types::timestamp::HasTimestampType;
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

/**
   A wrapper type that wraps a relay context with a target into a chain context.

   This allows the relay context to be used on components that require a chain context.
   The main use case is to wrap the relay context to implement [`CanSendMessages`].

   The relay context on its own can implement
   [`CanSendIbcMessages`](crate::relay::traits::components::ibc_message_sender::CanSendIbcMessages)
   but not [`CanSendMessages`], as the former is parameterized by a relay target.
   The two traits also have different charasteristics, as `CanSendIbcMessages` allows
   middleware components such as
   [`SendIbcMessagesWithUpdateClient`](crate::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
   to access the relay context and build `UpdateClient` messages to append to the
   front of incoming messages. On the other hand, [`CanSendMessages`] can only
   access the chain context but not the counterparty chain context, thus not able
   to build `UpdateClient` messages in the middle of the pipeline.

   With the `RelayToChain` wrapper, this allows the relay context to pretend that it
   is a chain context while also holding the counterparty chain context. The wrapper
   allows the relay context to be used with components that need to be polymorphic
   over any context that supports sending of messages, such as the batch worker
   component.
*/

pub struct RelayToChain<Relay, Target> {
    pub relay: Relay,
    pub phantom: PhantomData<Target>,
}

impl<Relay, Target> HasErrorType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type Error = Relay::Error;
}

impl<Relay, Target> HasMessageType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type Message = <Target::TargetChain as HasMessageType>::Message;
}

impl<Relay, Target> CanEstimateMessageSize for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    Target::TargetChain: CanEstimateMessageSize,
{
    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error> {
        Target::TargetChain::estimate_message_size(message).map_err(Target::target_chain_error)
    }
}

impl<Relay, Target> HasEventType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type Event = <Target::TargetChain as HasEventType>::Event;
}

impl<Relay, Target> HasHeightType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type Height = <Target::TargetChain as HasHeightType>::Height;
}

impl<Relay, Target> HasChainIdType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type ChainId = <Target::TargetChain as HasChainIdType>::ChainId;
}

impl<Relay, Target> HasTimestampType for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    type Timestamp = <Target::TargetChain as HasTimestampType>::Timestamp;
}

#[async_trait]
impl<Relay, Target> CanSendMessages for RelayToChain<Relay, Target>
where
    Relay: HasRelayChains,
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
            .map_err(Target::target_chain_error)
    }
}
