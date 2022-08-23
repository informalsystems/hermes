use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait BatchContext<Message, Event, Error>: Async {
    type MessagesSender: Async;
    type MessagesReceiver: Async;

    type ResultSender: Async;
    type ResultReceiver: Async;

    fn new_messages_channel(&self) -> (Self::MessagesSender, Self::MessagesReceiver);

    fn new_result_channel(&self) -> (Self::ResultSender, Self::ResultReceiver);

    fn send_messages(
        sender: &Self::MessagesSender,
        messages: Vec<Message>,
        result_sender: Self::ResultSender,
    );

    async fn try_receive_messages(
        receiver: &Self::MessagesReceiver,
    ) -> Result<Option<(Vec<Message>, Self::ResultSender)>, Error>;

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Event>>, Error>, Error>;

    fn send_result(result_sender: Self::ResultSender, events: Result<Vec<Vec<Event>>, Error>);
}

pub trait HasBatchContext<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type BatchContext: BatchContext<
        IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
        IbcEvent<Target::TargetChain, Target::CounterpartyChain>,
        Self::Error,
    >;

    fn batch_context(&self) -> &Self::BatchContext;

    fn messages_sender(
        &self,
    ) -> &<Self::BatchContext as BatchContext<
        IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
        IbcEvent<Target::TargetChain, Target::CounterpartyChain>,
        Self::Error,
    >>::MessagesSender;
}
