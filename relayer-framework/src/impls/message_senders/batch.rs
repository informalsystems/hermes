use alloc::collections::VecDeque;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::marker::PhantomData;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::Message as ChainMessage;
use crate::traits::message_channel::{
    HasChannelContext, OnceChannelContext, ReceiverOnceContext, SenderContext, SenderOnceContext,
    TryReceiverContext,
};
use crate::traits::relay_context::RelayContext;
use crate::traits::sleep::SleepContext;
use crate::traits::spawn::SpawnContext;
use crate::traits::target::ChainTarget;
use crate::traits::time::{Time, TimeContext};
use crate::types::aliases::{IbcEvent, IbcMessage};

#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub max_message_count: usize,
    pub max_tx_size: usize,
    pub buffer_size: usize,
    pub max_delay: Duration,
    pub sleep_time: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            max_message_count: 10,
            max_tx_size: 1000,
            buffer_size: 1000,
            max_delay: Duration::from_secs(1),
            sleep_time: Duration::from_millis(50),
        }
    }
}

pub struct ChannelClosedError;

pub trait BatchError {
    fn to_batch_error(&self) -> Self;
}

#[async_trait]
pub trait MessageResultSender<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn send_ok(
        self,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    );

    async fn send_error(self, err: Relay::Error);
}

#[async_trait]
pub trait MessageResultReceiver<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn receive_result(
        self,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>;
}

pub trait MessageBatch<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type ResultSender: MessageResultSender<Relay, Target>;
    type ResultReceiver: MessageResultReceiver<Relay, Target>;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (Self, Self::ResultReceiver);

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>;

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Self::ResultSender,
    );
}

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

pub struct BatchedMessageSender<InMessageSender>(PhantomData<InMessageSender>);

#[async_trait]
impl<Relay, Target, TargetChain, Batch, InMessageSender> IbcMessageSender<Relay, Target>
    for BatchedMessageSender<InMessageSender>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Relay: MessageBatchSender<Relay, Target, MessageBatch = Batch>,
    TargetChain: IbcChainContext<Target::CounterpartyChain>,
    Batch: MessageBatch<Relay, Target>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::IbcMessage>,
    ) -> Result<Vec<Vec<TargetChain::IbcEvent>>, Relay::Error> {
        let (batch, receiver) = MessageBatch::new(messages);

        context.send_message_batch(batch).await;

        let events = receiver.receive_result().await?;

        Ok(events)
    }
}

#[async_trait]
impl<Relay, Target, Channel, Sender> MessageResultSender<Relay, Target> for Sender
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Sender: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: SenderOnceContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = Sender,
    >,
{
    async fn send_ok(
        self,
        result: Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>,
    ) {
        let _ = Channel::send_once(self, Ok(result)).await;
    }

    async fn send_error(self, err: Relay::Error) {
        let _ = Channel::send_once(self, Err(err)).await;
    }
}

#[async_trait]
impl<Relay, Target, Channel, Receiver> MessageResultReceiver<Relay, Target> for Receiver
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Receiver: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: ReceiverOnceContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Receiver = Receiver,
    >,
    Relay::Error: From<ChannelClosedError>,
{
    async fn receive_result(
        self,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>
    {
        Channel::receive_once(self)
            .await
            .map_err(|_| ChannelClosedError)?
    }
}

impl<Relay, Target, Channel, Sender, Receiver> MessageBatch<Relay, Target>
    for (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Sender,
    )
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Sender: Async,
    Receiver: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = Sender,
        Receiver = Receiver,
    >,
    Relay::Error: From<ChannelClosedError>,
{
    type ResultSender = Sender;
    type ResultReceiver = Receiver;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (Self, Self::ResultReceiver) {
        let (sender, receiver) = Channel::new_channel();
        ((messages, sender), receiver)
    }

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>> {
        &self.0
    }

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Self::ResultSender,
    ) {
        (self.0, self.1)
    }
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
    Relay::Error: From<ChannelClosedError>,
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
    Relay::Error: From<ChannelClosedError>,
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
        let batch = Channel::try_receive(self)
            .await
            .map_err(|_| ChannelClosedError)?;

        Ok(batch)
    }
}

impl<InMessageSender> BatchedMessageSender<InMessageSender> {
    pub fn spawn_batch_message_handler<Relay, Target, Batch, BatchReceiver>(
        context: Arc<Relay>,
        config: BatchConfig,
        receiver: BatchReceiver,
    ) where
        Relay::Error: BatchError,
        Relay: TimeContext,
        Relay: RelayContext,
        Relay: SleepContext,
        Relay: SpawnContext,
        Target: ChainTarget<Relay>,
        InMessageSender: IbcMessageSender<Relay, Target>,
        Batch: MessageBatch<Relay, Target>,
        BatchReceiver: MessageBatchReceiver<Relay, Target, MessageBatch = Batch>,
    {
        let in_context = context.clone();
        context.spawn(async move {
            run_loop(
                in_context.as_ref(),
                PhantomData::<InMessageSender>,
                config.max_message_count,
                config.max_tx_size,
                config.max_delay,
                config.sleep_time,
                receiver,
            )
            .await;
        });
    }
}

async fn run_loop<Relay, Target, Batch, BatchReceiver, InMessageSender>(
    context: &Relay,
    in_sender: PhantomData<InMessageSender>,
    max_message_count: usize,
    max_tx_size: usize,
    max_delay: Duration,
    sleep_time: Duration,
    receiver: BatchReceiver,
) where
    Relay::Error: BatchError,
    Relay: TimeContext,
    Relay: RelayContext,
    Relay: SleepContext,
    Target: ChainTarget<Relay>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Batch: MessageBatch<Relay, Target>,
    BatchReceiver: MessageBatchReceiver<Relay, Target, MessageBatch = Batch>,
{
    let mut last_sent_time = context.now();
    let mut pending_batches = VecDeque::new();

    loop {
        match receiver.try_receive_message_batch().await {
            Ok(Some(batch)) => {
                pending_batches.push_back(batch);
                let current_batch_size = pending_batches.len();
                let now = context.now();

                pending_batches = process_message_batches(
                    context,
                    in_sender,
                    now,
                    &mut last_sent_time,
                    max_message_count,
                    max_tx_size,
                    max_delay,
                    pending_batches,
                )
                .await;

                if pending_batches.len() == current_batch_size {
                    context.sleep(sleep_time).await;
                }
            }
            Ok(None) => {}
            Err(_) => {
                return;
            }
        }
    }
}

async fn process_message_batches<Relay, Target, Batch, InMessageSender>(
    context: &Relay,
    in_sender: PhantomData<InMessageSender>,
    now: Relay::Time,
    last_sent_time: &mut Relay::Time,
    max_message_count: usize,
    max_tx_size: usize,
    max_delay: Duration,
    pending_batches: VecDeque<Batch>,
) -> VecDeque<Batch>
where
    Relay::Error: BatchError,
    Relay: TimeContext,
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Batch: MessageBatch<Relay, Target>,
{
    let batch_result = partition_message_batches(max_message_count, max_tx_size, pending_batches);

    if batch_result.ready_batches.is_empty() {
        // If there is nothing to send, return the remaining batches which should also be empty
        batch_result.remaining_batches
    } else if
    // If the current batch is not full and there is still some time until max delay,
    // return everything and wait until the next batch is full
    batch_result.remaining_batches.is_empty()
        && now.duration_since(last_sent_time) < max_delay
    {
        batch_result.ready_batches
    } else {
        send_ready_batches(context, in_sender, batch_result.ready_batches).await;
        *last_sent_time = now;

        batch_result.remaining_batches
    }
}

async fn send_ready_batches<Relay, Target, Batch, InMessageSender>(
    context: &Relay,
    _in_sender: PhantomData<InMessageSender>,
    ready_batches: VecDeque<Batch>,
) where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Batch: MessageBatch<Relay, Target>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Relay::Error: BatchError,
{
    let (messages, senders): (Vec<_>, Vec<_>) = ready_batches
        .into_iter()
        .map(|batch| {
            let (messages, result_sender) = batch.extract();
            let message_count = messages.len();
            (messages, (message_count, result_sender))
        })
        .unzip();

    let in_messages = messages.into_iter().flatten().collect::<Vec<_>>();

    let send_result = InMessageSender::send_messages(context, in_messages).await;

    match send_result {
        Err(e) => {
            for (_, sender) in senders.into_iter() {
                let _ = sender.send_error(e.to_batch_error());
            }
        }
        Ok(all_events) => {
            let mut all_events = all_events.into_iter();
            for (message_count, sender) in senders.into_iter() {
                let events = take(&mut all_events, message_count);
                let _ = sender.send_ok(events);
            }
        }
    }
}

struct BatchResult<Batch> {
    ready_batches: VecDeque<Batch>,
    remaining_batches: VecDeque<Batch>,
}

fn partition_message_batches<Relay, Target, Batch>(
    max_message_count: usize,
    max_tx_size: usize,
    batches: VecDeque<Batch>,
) -> BatchResult<Batch>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Batch: MessageBatch<Relay, Target>,
{
    let mut total_message_count: usize = 0;
    let mut total_batch_size: usize = 0;

    let (mut ready_batches, mut remaining_batches): (VecDeque<_>, _) =
        batches.into_iter().partition(|batch| {
            if total_message_count > max_message_count || total_batch_size > max_tx_size {
                false
            } else {
                let current_messages = batch.messages();
                let current_message_count = current_messages.len();
                let current_batch_size = batch_size(current_messages);

                if total_message_count + current_message_count > max_message_count
                    || total_batch_size + current_batch_size > max_tx_size
                {
                    false
                } else {
                    total_message_count += current_message_count;
                    total_batch_size += current_batch_size;

                    true
                }
            }
        });

    // If for some reason ready batch is empty but remaining batches is not,
    // it means there are single batch that are too big to fit in.
    // In that case put the first remaining batch as ready.
    if ready_batches.is_empty() && !remaining_batches.is_empty() {
        if let Some(batch) = remaining_batches.pop_front() {
            ready_batches.push_back(batch);
        }
    }

    BatchResult {
        ready_batches,
        remaining_batches,
    }
}

fn take<T, I: Iterator<Item = T>>(it: &mut I, count: usize) -> Vec<T> {
    let mut res = Vec::new();
    for _ in 0..count {
        match it.next() {
            Some(x) => {
                res.push(x);
            }
            None => {
                return res;
            }
        }
    }
    res
}

fn batch_size<Message: ChainMessage>(messages: &[Message]) -> usize {
    messages
        .iter()
        .map(|message| {
            // return 0 on encoding error, as we don't want
            // the batching operation to error out.
            message.estimate_len().unwrap_or(0)
        })
        .sum()
}
