use alloc::collections::VecDeque;
use core::mem;
use ibc_relayer_components::relay::traits::components::ibc_message_sender::CanSendIbcMessages;
use ibc_relayer_components::relay::traits::logs::logger::CanLogRelayTarget;

use async_trait::async_trait;
use ibc_relayer_components::chain::traits::types::chain::HasChainTypes;
use ibc_relayer_components::chain::traits::types::message::{
    CanEstimateMessageSize, HasMessageType,
};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;
use ibc_relayer_components::runtime::types::aliases::Runtime;

use crate::batch::types::aliases::{BatchSubmission, EventResultSender, MessageBatchReceiver};
use crate::batch::types::config::BatchConfig;
use crate::batch::types::sink::BatchWorkerSink;
use crate::runtime::traits::channel::{CanUseChannels, HasChannelTypes};
use crate::runtime::traits::channel_once::{CanUseChannelsOnce, HasChannelOnceTypes};
use crate::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};
use crate::std_prelude::*;

#[async_trait]
pub trait CanSpawnBatchMessageWorker<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasChannelTypes + HasChannelOnceTypes,
{
    fn spawn_batch_message_worker(
        self,
        target: Target,
        config: BatchConfig,
        receiver: MessageBatchReceiver<Target::TargetChain, Self::Error>,
    ) -> Box<dyn TaskHandle>;
}

impl<Relay, Target, Runtime> CanSpawnBatchMessageWorker<Target> for Relay
where
    Relay: CanRunLoop<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: HasSpawner + HasChannelTypes + HasChannelOnceTypes,
{
    fn spawn_batch_message_worker(
        self,
        _target: Target,
        config: BatchConfig,
        receiver: MessageBatchReceiver<Target::TargetChain, Self::Error>,
    ) -> Box<dyn TaskHandle> {
        let spawner = Target::target_chain(&self).runtime().spawner();

        spawner.spawn(async move {
            self.run_loop(&config, receiver).await;
        })
    }
}

#[async_trait]
trait CanRunLoop<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn run_loop(
        &self,
        config: &BatchConfig,
        receiver: MessageBatchReceiver<Target::TargetChain, Self::Error>,
    );
}

#[async_trait]
impl<Relay, Target, Runtime> CanRunLoop<Target> for Relay
where
    Relay: CanLogRelayTarget<Target> + CanProcessMessageBatches<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: HasTime + HasMutex + CanSleep + CanUseChannels + HasChannelOnceTypes,
{
    async fn run_loop(
        &self,
        config: &BatchConfig,
        mut receiver: MessageBatchReceiver<Target::TargetChain, Self::Error>,
    ) {
        let runtime = Target::target_chain(self).runtime();
        let mut pending_batches: VecDeque<BatchSubmission<Target::TargetChain, Self::Error>> =
            VecDeque::new();

        let mut last_sent_time = runtime.now();

        loop {
            let payload = Runtime::try_receive(&mut receiver);

            match payload {
                Ok(m_batch) => {
                    if let Some(batch) = m_batch {
                        let batch_size = batch.0.len();
                        self.log_relay_target(
                            Relay::Logger::LEVEL_TRACE,
                            "received message batch",
                            |log| {
                                log.display("batch_size", &batch_size);
                            },
                        );

                        pending_batches.push_back(batch);
                    }

                    let current_batch_size = pending_batches.len();
                    let now = runtime.now();

                    self.process_message_batches(
                        config,
                        &mut pending_batches,
                        now,
                        &mut last_sent_time,
                    )
                    .await;

                    if pending_batches.len() == current_batch_size {
                        runtime.sleep(config.sleep_time).await;
                    }
                }
                Err(e) => {
                    self.log_relay_target(
                        Relay::Logger::LEVEL_ERROR,
                        "error in try_receive, terminating worker",
                        |log| {
                            log.debug("error", &e);
                        },
                    );

                    return;
                }
            }
        }
    }
}

#[async_trait]
trait CanProcessMessageBatches<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasTime + HasChannelTypes + HasChannelOnceTypes,
{
    async fn process_message_batches(
        &self,
        config: &BatchConfig,
        pending_batches: &mut VecDeque<BatchSubmission<Target::TargetChain, Self::Error>>,
        now: <Runtime<Target::TargetChain> as HasTime>::Time,
        last_sent_time: &mut <Runtime<Target::TargetChain> as HasTime>::Time,
    );
}

#[async_trait]
impl<Relay, Target, Runtime> CanProcessMessageBatches<Target> for Relay
where
    Relay: CanLogRelayTarget<Target> + CanSendReadyBatches<Target> + Clone,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Target::TargetChain: CanPartitionMessageBatches<Relay::Error>,
    Runtime: HasTime + HasSpawner + HasChannelTypes + HasChannelOnceTypes,
{
    async fn process_message_batches(
        &self,
        config: &BatchConfig,
        pending_batches: &mut VecDeque<BatchSubmission<Target::TargetChain, Self::Error>>,
        now: Runtime::Time,
        last_sent_time: &mut Runtime::Time,
    ) {
        let ready_batches = Target::TargetChain::partition_message_batches(config, pending_batches);

        if ready_batches.is_empty() {
            // If there is nothing to send, return the remaining batches which should also be empty
        } else if pending_batches.is_empty()
            && Runtime::duration_since(&now, last_sent_time) < config.max_delay
        {
            // If the current batch is not full and there is still some time until max delay,
            // return everything and wait until the next batch is full
            *pending_batches = ready_batches;
        } else {
            let batch_size = ready_batches.len();
            self.log_relay_target(Relay::Logger::LEVEL_TRACE, "sending ready batches", |log| {
                log.display("batch_size", &batch_size);
            });

            let spawner = Target::target_chain(self).runtime().spawner();
            let relay = self.clone();

            spawner.spawn(async move {
                relay.send_ready_batches(ready_batches).await;
            });

            *last_sent_time = now;
        }
    }
}

trait CanPartitionMessageBatches<Error>: HasChainTypes + HasRuntime
where
    Error: Async,
    Self::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    fn partition_message_batches(
        config: &BatchConfig,
        pending_batches: &mut VecDeque<BatchSubmission<Self, Error>>,
    ) -> VecDeque<(Vec<Self::Message>, EventResultSender<Self, Error>)>;
}

impl<Chain, Error, Runtime> CanPartitionMessageBatches<Error> for Chain
where
    Error: Async,
    Chain: HasChainTypes + HasRuntime<Runtime = Runtime>,
    Chain: CanEstimateBatchSize,
    Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    fn partition_message_batches(
        config: &BatchConfig,
        pending_batches: &mut VecDeque<BatchSubmission<Chain, Error>>,
    ) -> VecDeque<(Vec<Chain::Message>, EventResultSender<Chain, Error>)> {
        let batches = mem::take(pending_batches);

        let mut total_message_count: usize = 0;
        let mut total_batch_size: usize = 0;

        let (mut ready_batches, mut remaining_batches): (VecDeque<_>, _) = batches
            .into_iter()
            .partition(|(current_messages, _sender)| {
                if total_message_count > config.max_message_count
                    || total_batch_size > config.max_tx_size
                {
                    false
                } else {
                    let current_message_count = current_messages.len();
                    let current_batch_size = Chain::estimate_batch_size(current_messages);

                    if total_message_count + current_message_count > config.max_message_count
                        || total_batch_size + current_batch_size > config.max_tx_size
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

        *pending_batches = remaining_batches;

        ready_batches
    }
}

#[async_trait]
trait CanSendReadyBatches<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn send_ready_batches(
        &self,
        ready_batches: VecDeque<BatchSubmission<Target::TargetChain, Self::Error>>,
    );
}

#[async_trait]
impl<Relay, Target, Runtime> CanSendReadyBatches<Target> for Relay
where
    Relay: CanLogRelayTarget<Target> + CanSendIbcMessages<BatchWorkerSink, Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanUseChannelsOnce + CanUseChannels,
    Relay::Error: Clone,
{
    async fn send_ready_batches(
        &self,
        ready_batches: VecDeque<BatchSubmission<Target::TargetChain, Self::Error>>,
    ) {
        let (messages, senders): (Vec<_>, Vec<_>) = ready_batches
            .into_iter()
            .map(|(messages, result_sender)| {
                let message_count = messages.len();
                (messages, (message_count, result_sender))
            })
            .unzip();

        let in_messages = messages.into_iter().flatten().collect::<Vec<_>>();

        let message_count = in_messages.len();

        self.log_relay_target(
            Relay::Logger::LEVEL_TRACE,
            "sending batched messages to inner sender",
            |log| {
                log.display("message_count", &message_count);
            },
        );

        let send_result = self.send_messages(Target::default(), in_messages).await;

        match send_result {
            Err(e) => {
                self.log_relay_target(
                    Relay::Logger::LEVEL_TRACE,
                    "inner sender returned error result, sending error back to caller",
                    |log| {
                        log.debug("error", &e);
                    },
                );

                for (_, sender) in senders.into_iter() {
                    let _ = Runtime::send_once(sender, Err(e.clone()));
                }
            }
            Ok(all_events) => {
                let events_count = all_events.len();
                let mut all_events = all_events.into_iter();

                self.log_relay_target(
                    Relay::Logger::LEVEL_TRACE,
                    "inner sender returned result events, sending events back to caller",
                    |log| {
                        log.display("events_count", &events_count);
                    },
                );

                for (message_count, sender) in senders.into_iter() {
                    let events = take(&mut all_events, message_count);
                    let _ = Runtime::send_once(sender, Ok(events));
                }
            }
        }
    }
}

trait CanEstimateBatchSize: HasMessageType {
    fn estimate_batch_size(messages: &[Self::Message]) -> usize;
}

impl<Chain> CanEstimateBatchSize for Chain
where
    Chain: CanEstimateMessageSize,
{
    fn estimate_batch_size(messages: &[Self::Message]) -> usize {
        messages
            .iter()
            .map(|message| {
                // return 0 on encoding error, as we don't want
                // the batching operation to error out.
                Chain::estimate_message_size(message).unwrap_or(0)
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
