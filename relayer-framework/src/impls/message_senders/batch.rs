use alloc::collections::VecDeque;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::marker::PhantomData;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::contexts::chain::IbcChainContext;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::Message as ChainMessage;
use crate::traits::runtime::sleep::SleepContext;
use crate::traits::runtime::spawn::SpawnContext;
use crate::traits::runtime::time::{Time, TimeContext};
use crate::traits::target::ChainTarget;

mod message_batch;
mod message_batch_channel;
mod message_result_channel;

use self::message_batch::MessageBatch;
use self::message_batch_channel::MessageBatchChannel;
use self::message_result_channel::MessageResultChannel;

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

pub trait BatchError {
    fn to_batch_error(&self) -> Self;
}

pub trait BatchedMessageContext<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type MessageBatchChannel: MessageBatchChannel<Self, Target>;

    fn message_batch_sender(
        &self,
    ) -> &<Self::MessageBatchChannel as MessageBatchChannel<Self, Target>>::Sender;
}

pub struct BatchedMessageSender<Channel, InMessageSender>(PhantomData<(Channel, InMessageSender)>);

#[async_trait]
impl<Relay, Target, TargetChain, Batch, InMessageSender, Channel> IbcMessageSender<Relay, Target>
    for BatchedMessageSender<Channel, InMessageSender>
where
    Relay: RelayContext,
    Relay: BatchedMessageContext<Target, MessageBatchChannel = Channel>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Channel: MessageBatchChannel<Relay, Target, MessageBatch = Batch>,
    TargetChain: IbcChainContext<Target::CounterpartyChain>,
    Batch: MessageBatch<Relay, Target>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::IbcMessage>,
    ) -> Result<Vec<Vec<TargetChain::IbcEvent>>, Relay::Error> {
        let (batch, receiver) = MessageBatch::new(messages);

        Channel::send_message_batch(context.message_batch_sender(), batch).await;

        let events = Batch::Channel::receive_result(receiver).await?;

        Ok(events)
    }
}

impl<Channel, InMessageSender> BatchedMessageSender<Channel, InMessageSender> {
    pub fn spawn_batch_message_handler<Relay, Target, Batch>(
        context: Arc<Relay>,
        config: BatchConfig,
        receiver: Channel::Receiver,
    ) where
        Relay::Error: BatchError,
        Relay: TimeContext,
        Relay: RelayContext,
        Relay: SleepContext,
        Relay: SpawnContext,
        Target: ChainTarget<Relay>,
        InMessageSender: IbcMessageSender<Relay, Target>,
        Batch: MessageBatch<Relay, Target>,
        Channel: MessageBatchChannel<Relay, Target, MessageBatch = Batch>,
    {
        let in_context = context.clone();
        context.spawn(async move {
            run_loop(
                in_context.as_ref(),
                PhantomData::<Channel>,
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

async fn run_loop<Relay, Target, Batch, Channel, InMessageSender>(
    context: &Relay,
    _channel: PhantomData<Channel>,
    in_sender: PhantomData<InMessageSender>,
    max_message_count: usize,
    max_tx_size: usize,
    max_delay: Duration,
    sleep_time: Duration,
    receiver: Channel::Receiver,
) where
    Relay::Error: BatchError,
    Relay: TimeContext,
    Relay: RelayContext,
    Relay: SleepContext,
    Target: ChainTarget<Relay>,
    InMessageSender: IbcMessageSender<Relay, Target>,
    Batch: MessageBatch<Relay, Target>,
    Channel: MessageBatchChannel<Relay, Target, MessageBatch = Batch>,
{
    let mut last_sent_time = context.now();
    let mut pending_batches = VecDeque::new();

    loop {
        match Channel::try_receive_message_batch(&receiver).await {
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
                let _ = Batch::Channel::send_error(sender, e.to_batch_error());
            }
        }
        Ok(all_events) => {
            let mut all_events = all_events.into_iter();
            for (message_count, sender) in senders.into_iter() {
                let events = take(&mut all_events, message_count);
                let _ = Batch::Channel::send_ok(sender, events);
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
