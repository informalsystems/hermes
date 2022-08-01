use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::message_channel::{
    HasChannelContext, OnceChannelContext, SenderContext, TryReceiverContext,
};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

use super::message_batch::MessageBatch;

#[async_trait]
pub trait MessageBatchSender<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type MessageBatch: MessageBatch<Relay, Target>;

    async fn send_message_batch(&self, batch: Self::MessageBatch);
}

#[async_trait]
pub trait MessageBatchReceiver<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type MessageBatch: MessageBatch<Relay, Target>;

    async fn try_receive_message_batch(&self) -> Result<Option<Self::MessageBatch>, Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Channel, ResultSender, BatchSender> MessageBatchSender<Relay, Target>
    for BatchSender
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    ResultSender: Async,
    BatchSender: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = ResultSender,
    >,
    Relay::Error: From<Channel::Error>,
    Channel: SenderContext<
        (
            Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
            ResultSender,
        ),
        Sender = BatchSender,
    >,
{
    type MessageBatch = (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        ResultSender,
    );

    async fn send_message_batch(&self, batch: Self::MessageBatch) {
        let _ = Channel::send(self, batch).await;
    }
}

#[async_trait]
impl<Relay, Target, Channel, ResultSender, BatchReceiver> MessageBatchReceiver<Relay, Target>
    for BatchReceiver
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    ResultSender: Async,
    BatchReceiver: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = ResultSender,
    >,
    Relay::Error: From<Channel::Error>,
    Channel: TryReceiverContext<
        (
            Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
            ResultSender,
        ),
        Receiver = BatchReceiver,
    >,
{
    type MessageBatch = (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        ResultSender,
    );

    async fn try_receive_message_batch(&self) -> Result<Option<Self::MessageBatch>, Relay::Error> {
        let batch = Channel::try_receive(self).await?;

        Ok(batch)
    }
}
