use alloc::collections::VecDeque;
use core::marker::PhantomData;
use core::mem;

use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::{
    CanUseChannels, CanUseChannelsOnce, HasChannelOnceTypes, HasChannelTypes,
};
use crate::base::runtime::traits::log::{HasLogger, LevelDebug};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::base::runtime::traits::time::HasTime;
use crate::full::batch::traits::channel::HasMessageBatchReceiver;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::batch::types::aliases::{BatchSubmission, EventResultSender};
use crate::full::batch::types::config::BatchConfig;
use crate::std_prelude::*;

pub struct BatchMessageWorker<Relay, Target>
where
    Relay: HasRelayTypes,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    pub relay: Relay,
    pub pending_batches: VecDeque<BatchSubmission<Target::TargetChain, Relay::Error>>,
    pub config: BatchConfig,
    pub phantom: PhantomData<Target>,
}

impl<Relay, Target, TargetChain, Message, Event, Runtime, Error> BatchMessageWorker<Relay, Target>
where
    Relay: HasRelayTypes<Error = Error>,
    Relay: HasMessageBatchReceiver<Target>,
    Relay: HasRuntime<Runtime = Runtime>,
    TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Runtime: CanUseChannelsOnce + CanUseChannels,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain, Message = Message, Event = Event>,
    Event: Async,
    Error: Clone + Async,
    Message: Async,
{
    pub fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        let spawner = relay.runtime().spawner();

        let mut handler = Self {
            relay,
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
            match Runtime::try_receive(self.relay.get_batch_receiver()).await {
                Ok(m_batch) => {
                    if let Some(batch) = m_batch {
                        self.relay
                            .runtime()
                            .log(LevelDebug, "received message batch")
                            .await;
                        self.pending_batches.push_back(batch);
                    }

                    let current_batch_size = self.pending_batches.len();
                    let now = self.relay.runtime().now();

                    self.process_message_batches(now, &mut last_sent_time).await;

                    if self.pending_batches.len() == current_batch_size {
                        self.relay.runtime().sleep(self.config.sleep_time).await;
                    }
                }
                Err(_) => {
                    self.relay
                        .runtime()
                        .log(LevelDebug, "error in try_receive, terminating worker")
                        .await;
                    return;
                }
            }
        }
    }

    async fn process_message_batches(
        &mut self,
        now: Runtime::Time,
        last_sent_time: &mut Runtime::Time,
    ) {
        let ready_batches = self.partition_message_batches();

        if ready_batches.is_empty() {
            // If there is nothing to send, return the remaining batches which should also be empty
        } else if self.pending_batches.is_empty()
            && Runtime::duration_since(&now, last_sent_time) < self.config.max_delay
        {
            // If the current batch is not full and there is still some time until max delay,
            // return everything and wait until the next batch is full
            self.relay
                .runtime()
                .log(LevelDebug, "waiting for more batch to arrive")
                .await;
            self.pending_batches = ready_batches;
        } else {
            self.relay
                .runtime()
                .log(LevelDebug, "sending reading batches")
                .await;
            Self::send_ready_batches(&self.relay, ready_batches).await;
            *last_sent_time = now;
        }
    }

    fn partition_message_batches(
        &mut self,
    ) -> VecDeque<(Vec<Message>, EventResultSender<TargetChain, Error>)> {
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

    async fn send_ready_batches(
        relay: &Relay,
        ready_batches: VecDeque<BatchSubmission<TargetChain, Error>>,
    ) {
        let (messages, senders): (Vec<_>, Vec<_>) = ready_batches
            .into_iter()
            .map(|(messages, result_sender)| {
                let message_count = messages.len();
                (messages, (message_count, result_sender))
            })
            .unzip();

        let in_messages = messages.into_iter().flatten().collect::<Vec<_>>();

        relay
            .runtime()
            .log(LevelDebug, "sending batched messages to inner sender")
            .await;

        let send_result = relay.send_messages_from_batch_worker(in_messages).await;

        match send_result {
            Err(e) => {
                for (_, sender) in senders.into_iter() {
                    let _ = Runtime::send_once(sender, Err(e.clone()));
                }
            }
            Ok(all_events) => {
                let mut all_events = all_events.into_iter();
                for (message_count, sender) in senders.into_iter() {
                    let events = take(&mut all_events, message_count);
                    let _ = Runtime::send_once(sender, Ok(events));
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
                TargetChain::estimate_message_len(message).unwrap_or(0)
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
