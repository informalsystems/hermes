use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::chain::traits::types::{HasChainTypes, HasEventType, HasMessageType};
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::{
    CanCreateChannels, CanUseChannels, CanUseChannelsOnce,
};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::traits::channel::HasBatchChannelTypes;
use crate::full::batch::types::{
    EventResultReceiver, EventResultSender, MessageBatchReceiver, MessageBatchSender,
};
use crate::std_prelude::*;

pub struct BatchChannelsForRelay<Relay, Target>(PhantomData<(Relay, Target)>);

impl<Relay, Target, Chain> HasErrorType for BatchChannelsForRelay<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = Chain>,
    Chain: HasErrorType,
{
    type Error = Chain::Error;
}

impl<Relay, Target, Chain> HasMessageType for BatchChannelsForRelay<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = Chain>,
    Chain: HasMessageType,
{
    type Message = Chain::Message;
}

impl<Relay, Target, Chain> HasEventType for BatchChannelsForRelay<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = Chain>,
    Chain: HasEventType,
{
    type Event = Chain::Event;
}

#[async_trait]
impl<Relay, Target, Chain, Runtime> HasBatchChannelTypes for BatchChannelsForRelay<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = Chain>,
    Chain: HasRuntime<Runtime = Runtime>,
    Chain: HasChainTypes,
    Runtime: CanCreateChannels + CanUseChannelsOnce + CanUseChannels,
{
    type SendMessageError = Relay::Error;

    type BatchSender = MessageBatchSender<Relay, Target>;
    type BatchReceiver = MessageBatchReceiver<Relay, Target>;

    type ResultSender = EventResultSender<Relay, Target>;
    type ResultReceiver = EventResultReceiver<Relay, Target>;

    fn new_batch_channel() -> (Self::BatchSender, Self::BatchReceiver) {
        Runtime::new_channel()
    }

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver) {
        Runtime::new_channel()
    }

    fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Self::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Self::Error> {
        Runtime::send(sender, (messages, result_sender)).map_err(Chain::runtime_error)
    }

    async fn try_receive_batch(
        receiver: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::ResultSender)>, Self::Error> {
        Runtime::try_receive(receiver)
            .await
            .map_err(Chain::runtime_error)
    }

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Self::Event>>, Self::SendMessageError>, Self::Error> {
        Runtime::receive_once(result_receiver)
            .await
            .map_err(Chain::runtime_error)
    }

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Self::Event>>, Self::SendMessageError>,
    ) -> Result<(), Self::Error> {
        Runtime::send_once(result_sender, events).map_err(Chain::runtime_error)
    }
}
