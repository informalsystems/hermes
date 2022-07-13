use alloc::collections::VecDeque;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::marker::PhantomData;
use core::time::Duration;
use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::ibc_message_sender::IbcMessageSender;
use ibc_relayer_framework::traits::message::Message as ChainMessage;
use ibc_relayer_framework::traits::relay_context::RelayContext;
use ibc_relayer_framework::traits::target::ChainTarget;
use ibc_relayer_framework::types::aliases::{IbcEvent, IbcMessage};
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::sync::mpsc::{error::TryRecvError, Receiver, Sender};
use tokio::sync::oneshot::{channel as once_channel, Sender as OnceSender};
use tokio::time::sleep;

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

pub struct BatchedMessageSender<Sender>(PhantomData<Sender>);

pub struct MessageBatch<Chain, Counterparty>
where
    Chain: IbcChainContext<Counterparty>,
    Counterparty: ChainContext,
{
    messages: Vec<IbcMessage<Chain, Counterparty>>,
    result_sender: OnceSender<Result<Vec<Vec<IbcEvent<Chain, Counterparty>>>, Chain::Error>>,
}

pub trait BatchMessageContext<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    fn message_sink(&self)
        -> &Sender<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>;
}

pub trait BatchError {
    fn to_batch_error(&self) -> Self;
}

#[async_trait]
impl<Relay, Target, TargetChain, Message, Event, Error, Sender> IbcMessageSender<Relay, Target>
    for BatchedMessageSender<Sender>
where
    Message: Async,
    Event: Async,
    Error: Async,
    Sender: Async,
    Error: From<ChannelClosedError>,
    Relay: RelayContext<Error = Error>,
    Relay: BatchMessageContext<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<
        Target::CounterpartyChain,
        IbcMessage = Message,
        IbcEvent = Event,
        Error = Error,
    >,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        let (result_sender, receiver) = once_channel();

        let batch = MessageBatch {
            messages,
            result_sender,
        };

        context
            .message_sink()
            .send(batch)
            .await
            .map_err(|_| ChannelClosedError)?;

        let events = receiver.await.map_err(|_| ChannelClosedError)??;

        Ok(events)
    }
}

impl<Sender> BatchedMessageSender<Sender> {
    pub fn spawn_batch_message_handler<Relay, Target>(
        context: Arc<Relay>,
        config: BatchConfig,
        runtime: &Runtime,
        receiver: Receiver<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>,
    ) where
        Relay: RelayContext,
        Target: ChainTarget<Relay>,
        Sender: IbcMessageSender<Relay, Target>,
        Relay::Error: BatchError,
    {
        runtime.spawn(async move {
            Self::run_loop(
                &context,
                config.max_message_count,
                config.max_tx_size,
                config.max_delay,
                config.sleep_time,
                receiver,
            )
            .await;
        });
    }

    async fn run_loop<Relay, Target>(
        context: &Relay,
        max_message_count: usize,
        max_tx_size: usize,
        max_delay: Duration,
        sleep_time: Duration,
        mut receiver: Receiver<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>,
    ) where
        Relay::Error: BatchError,
        Relay: RelayContext,
        Target: ChainTarget<Relay>,
        Sender: IbcMessageSender<Relay, Target>,
    {
        let mut last_sent_time = Instant::now();
        let mut pending_batches = VecDeque::new();

        loop {
            match receiver.try_recv() {
                Ok(batch) => {
                    pending_batches.push_back(batch);
                    let current_batch_size = pending_batches.len();
                    pending_batches = Self::process_message_batches(
                        context,
                        max_message_count,
                        max_tx_size,
                        max_delay,
                        &mut last_sent_time,
                        pending_batches,
                    )
                    .await;

                    if pending_batches.len() == current_batch_size {
                        sleep(sleep_time).await;
                    }
                }
                Err(TryRecvError::Empty) => {
                    sleep(sleep_time).await;
                }
                Err(TryRecvError::Disconnected) => {
                    return;
                }
            }
        }
    }

    async fn process_message_batches<Relay, Target>(
        context: &Relay,
        max_message_count: usize,
        max_tx_size: usize,
        max_delay: Duration,
        last_sent_time: &mut Instant,
        pending_batches: VecDeque<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> VecDeque<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>
    where
        Relay::Error: BatchError,
        Relay: RelayContext,
        Target: ChainTarget<Relay>,
        Sender: IbcMessageSender<Relay, Target>,
    {
        let batch_result =
            partition_message_batches(max_message_count, max_tx_size, pending_batches);

        let now = Instant::now();

        if batch_result.ready_batches.is_empty() {
            // If there is nothing to send, return the remaining batches which should also be empty
            batch_result.remaining_batches
        } else if
        // If the current batch is not full and there is still some time until max delay,
        // return everything and wait until the next batch is full
        batch_result.remaining_batches.is_empty()
            && now.duration_since(*last_sent_time) < max_delay
        {
            batch_result.ready_batches
        } else {
            Self::send_ready_batches(context, batch_result.ready_batches).await;
            *last_sent_time = now;

            batch_result.remaining_batches
        }
    }

    async fn send_ready_batches<Relay, Target, Message, Event, Error>(
        context: &Relay,
        ready_batches: VecDeque<MessageBatch<Target::TargetChain, Target::CounterpartyChain>>,
    ) where
        Relay: RelayContext<Error = Error>,
        Target: ChainTarget<Relay>,
        Sender: IbcMessageSender<Relay, Target>,
        Target::TargetChain:
            IbcChainContext<Target::CounterpartyChain, IbcMessage = Message, IbcEvent = Event>,
        Error: BatchError,
    {
        let (messages, senders): (Vec<_>, Vec<_>) = ready_batches
            .into_iter()
            .map(|batch| {
                let message_count = batch.messages.len();
                (batch.messages, (message_count, batch.result_sender))
            })
            .unzip();

        let in_messages = messages.into_iter().flatten().collect::<Vec<_>>();

        let send_result = Sender::send_messages(context, in_messages).await;

        match send_result {
            Err(e) => {
                for (_, sender) in senders.into_iter() {
                    let _ = sender.send(Err(e.to_batch_error()));
                }
            }
            Ok(all_events) => {
                let mut all_events = all_events.into_iter();
                for (message_count, sender) in senders.into_iter() {
                    let events = take(&mut all_events, message_count);
                    let _ = sender.send(Ok(events));
                }
            }
        }
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

struct BatchResult<Chain, Counterparty>
where
    Chain: IbcChainContext<Counterparty>,
    Counterparty: ChainContext,
{
    ready_batches: VecDeque<MessageBatch<Chain, Counterparty>>,
    remaining_batches: VecDeque<MessageBatch<Chain, Counterparty>>,
}

fn partition_message_batches<Chain, Counterparty>(
    max_message_count: usize,
    max_tx_size: usize,
    batches: VecDeque<MessageBatch<Chain, Counterparty>>,
) -> BatchResult<Chain, Counterparty>
where
    Chain: IbcChainContext<Counterparty>,
    Counterparty: ChainContext,
{
    let mut total_message_count: usize = 0;
    let mut total_batch_size: usize = 0;

    let (mut ready_batches, mut remaining_batches): (VecDeque<_>, _) =
        batches.into_iter().partition(|batch| {
            if total_message_count > max_message_count || total_batch_size > max_tx_size {
                false
            } else {
                let current_message_count = batch.messages.len();
                let current_batch_size = batch_size(&batch.messages);

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
        remaining_batches.pop_front().and_then(|batch| {
            ready_batches.push_back(batch);
            Some(())
        });
    }

    BatchResult {
        ready_batches,
        remaining_batches,
    }
}
