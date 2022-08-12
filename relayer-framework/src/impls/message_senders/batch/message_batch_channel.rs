use core::marker::PhantomData;

use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::traits::message_channel::{MultiChannelContext, OnceChannelContext};
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

use super::message_batch::MessageBatch;

#[async_trait]
pub trait MessageBatchChannel<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type Sender: Async;
    type Receiver: Async;
    type MessageBatch: MessageBatch<Relay, Target>;

    async fn send_message_batch(sender: &Self::Sender, batch: Self::MessageBatch);

    async fn try_receive_message_batch(
        receiver: &Self::Receiver,
    ) -> Result<Option<Self::MessageBatch>, Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Channel, ResultSender, BatchSender, BatchReceiver>
    MessageBatchChannel<Relay, Target> for Channel
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    BatchSender: Async,
    BatchReceiver: Async,
    ResultSender: Async,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = ResultSender,
    >,
    Relay::Error: From<Channel::Error>,
    Channel: MultiChannelContext<
        (
            Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
            ResultSender,
            PhantomData<Channel>,
        ),
        Sender = BatchSender,
        Receiver = BatchReceiver,
    >,
{
    type Sender = BatchSender;
    type Receiver = BatchReceiver;

    type MessageBatch = (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        ResultSender,
        PhantomData<Channel>,
    );

    async fn send_message_batch(sender: &BatchSender, batch: Self::MessageBatch) {
        let _ = Channel::send(sender, batch).await;
    }

    async fn try_receive_message_batch(
        receiver: &BatchReceiver,
    ) -> Result<Option<Self::MessageBatch>, Relay::Error> {
        let batch = Channel::try_receive(receiver).await?;

        Ok(batch)
    }
}

// #[async_trait]
// impl<Relay, Target, Channel, ResultSender, BatchReceiver> MessageBatchReceiver<Relay, Target>
//     for BatchReceiver
// where
//     Relay: RelayContext,
//     Target: ChainTarget<Relay>,
//     ResultSender: Async,
//     BatchReceiver: Async,
//     Relay: HasChannel<ChannelContext = Channel>,
//     Channel: OnceChannelContext<
//         Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
//         Sender = ResultSender,
//     >,
//     Relay::Error: From<Channel::Error>,
//     Channel: TryReceiverContext<
//         (
//             Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
//             ResultSender,
//         ),
//         Receiver = BatchReceiver,
//     >,
// {
//     type MessageBatch = (
//         Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
//         ResultSender,
//     );

// }
