use alloc::collections::VecDeque;
use core::marker::PhantomData;
use core::mem;

use crate::std_prelude::*;
use crate::traits::contexts::chain::IbcChainContext;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::Message as SomeMessage;
use crate::traits::runtime::sleep::CanSleep;
use crate::traits::runtime::spawn::{HasSpawner, Spawner};
use crate::traits::runtime::time::{HasTime, Time};
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

use super::config::BatchConfig;
use super::context::{BatchContext, HasBatchContext};
use super::error::BatchError;

pub struct BatchMessageHandler<Relay, Target, Sender, Batch>
where
    Relay: RelayContext,
    Relay: HasBatchContext<Target, BatchContext = Batch>,
    Target: ChainTarget<Relay>,
    Sender: IbcMessageSender<Relay, Target>,
    Batch: BatchContext<
        IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
        IbcEvent<Target::TargetChain, Target::CounterpartyChain>,
        Relay::Error,
    >,
{
    pub relay: Relay,
    pub messages_receiver: Batch::MessagesReceiver,
    pub pending_batches: VecDeque<(
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Batch::ResultSender,
    )>,
    pub config: BatchConfig,
    pub phantom: PhantomData<(Target, Sender)>,
}

impl<Relay, Target, Sender, Batch, TargetChain, Message, Event, Runtime, Error>
    BatchMessageHandler<Relay, Target, Sender, Batch>
where
    Relay: RelayContext<Runtime = Runtime, Error = Error>,
    Runtime: HasTime + CanSleep + HasSpawner,
    Relay: HasBatchContext<Target, BatchContext = Batch>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    Sender: IbcMessageSender<Relay, Target>,
    Batch: BatchContext<Message, Event, Error>,
    Message: SomeMessage,
    Event: Async,
    TargetChain: IbcChainContext<Target::CounterpartyChain, IbcMessage = Message, IbcEvent = Event>,
    Error: BatchError,
{
    pub fn spawn_batch_message_handler(
        relay: Relay,
        config: BatchConfig,
        messages_receiver: Batch::MessagesReceiver,
    ) {
        let spawner = relay.runtime().spawner();

        let mut handler = Self {
            relay,
            messages_receiver,
            pending_batches: VecDeque::new(),
            config,
            phantom: PhantomData,
        };

        spawner.spawn(async move {
            handler.run_loop().await;
        });
    }

    async fn run_loop(&mut self) {
        let mut last_sent_time = self.relay.runtime().now();

        loop {
            match Batch::try_receive_messages(&self.messages_receiver).await {
                Ok(Some(batch)) => {
                    self.pending_batches.push_back(batch);
                    let current_batch_size = self.pending_batches.len();
                    let now = self.relay.runtime().now();

                    self.process_message_batches(now, &mut last_sent_time).await;

                    if self.pending_batches.len() == current_batch_size {
                        self.relay.runtime().sleep(self.config.sleep_time).await;
                    }
                }
                Ok(None) => {}
                Err(_) => {
                    return;
                }
            }
        }
    }

    pub async fn process_message_batches(
        &mut self,
        now: Runtime::Time,
        last_sent_time: &mut Runtime::Time,
    ) {
        let ready_batches = self.partition_message_batches();

        if !ready_batches.is_empty() {
            // If there is nothing to send, return the remaining batches which should also be empty
        } else if self.pending_batches.is_empty()
            && now.duration_since(last_sent_time) < self.config.max_delay
        {
            // If the current batch is not full and there is still some time until max delay,
            // return everything and wait until the next batch is full
        } else {
            Self::send_ready_batches(&self.relay, ready_batches).await;
            *last_sent_time = now;
        }
    }

    fn partition_message_batches(&mut self) -> VecDeque<(Vec<Message>, Batch::ResultSender)> {
        let batches = mem::take(&mut self.pending_batches);

        let mut total_message_count: usize = 0;
        let mut total_batch_size: usize = 0;

        let (mut ready_batches, mut remaining_batches): (VecDeque<_>, _) = batches
            .into_iter()
            .partition(|(current_messages, _sender)| {
                if total_message_count > self.config.max_message_count
                    || total_batch_size > self.config.max_tx_size
                {
                    false
                } else {
                    let current_message_count = current_messages.len();
                    let current_batch_size = Self::batch_size(current_messages);

                    if total_message_count + current_message_count > self.config.max_message_count
                        || total_batch_size + current_batch_size > self.config.max_tx_size
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

        self.pending_batches = remaining_batches;

        ready_batches
    }

    pub async fn send_ready_batches(
        context: &Relay,
        ready_batches: VecDeque<(Vec<Message>, Batch::ResultSender)>,
    ) {
        let (messages, senders): (Vec<_>, Vec<_>) = ready_batches
            .into_iter()
            .map(|(messages, result_sender)| {
                let message_count = messages.len();
                (messages, (message_count, result_sender))
            })
            .unzip();

        let in_messages = messages.into_iter().flatten().collect::<Vec<_>>();

        let send_result = Sender::send_messages(context, in_messages).await;

        match send_result {
            Err(e) => {
                for (_, sender) in senders.into_iter() {
                    let _ = Batch::send_result(sender, Err(e.as_batch_error()));
                }
            }
            Ok(all_events) => {
                let mut all_events = all_events.into_iter();
                for (message_count, sender) in senders.into_iter() {
                    let events = take(&mut all_events, message_count);
                    let _ = Batch::send_result(sender, Ok(events));
                }
            }
        }
    }

    fn batch_size(messages: &[Message]) -> usize {
        messages
            .iter()
            .map(|message| {
                // return 0 on encoding error, as we don't want
                // the batching operation to error out.
                message.estimate_len().unwrap_or(0)
            })
            .sum()
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
