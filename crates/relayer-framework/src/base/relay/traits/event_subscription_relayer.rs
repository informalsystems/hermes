use async_trait::async_trait;
use futures::stream::StreamExt;

use crate::base::chain::types::aliases::{EventSubscription, Runtime};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::event_relayer::CanRelayEvent;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::subscription::{CanSubscribe, HasSubscriptionType};
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

/**
   An event subscription relayer performs event relaying based on a given
   [`Subscription`](HasSubscriptionType::Subscription) of events.

   The relayer performs the relaying by subscribing to the event subscription,
   and then delegate the relaying of individual events to [`CanRelayEvent`].

   Different implementation of [`EventSubscriptionRelayer`] may employ
   different strategies of relaying multiple events. For example,
   [`SequentialEventSubscriptionRelayer`] relays only one packet at a time,
   while [`ConcurrentEventSubscriptionRelayer`] allows relaying of multiple
   events concurrently.
*/
#[async_trait]
pub trait EventSubscriptionRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasSubscriptionType,
{
    async fn relay_chain_event_subscription(
        relayer: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}

/**
   A sequential implementation of [`EventSubscriptionRelayer`]. With a given
   event subscription, the relayer blocks on relaying one event, and only
   continues relaying the other event after the current event is fully relayed.

   This can be very inefficient for production relayers, but it can be useful
   for testing purposes, or for restricted environments such as in Wasm. The
   relayer is also useful if event filters are set up such that only small
   number of events are processed, such as building a wallet-specific relayer.
*/
struct SequentialEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target, Runtime> EventSubscriptionRelayer<Relay, Target>
    for SequentialEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSubscribe,
{
    async fn relay_chain_event_subscription(
        relay: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        loop {
            if let Some(event_stream) = Runtime::subscribe(&event_subscription) {
                // Use [`StreamExt::foreach`] to process the events sequentially.
                event_stream
                    .for_each(|item| async move {
                        let (height, event) = item.as_ref();

                        // Ignore any relaying errors, as the relayer still needs to proceed
                        // relaying the next event regardless.
                        let _ = relay.relay_chain_event(&height, &event).await;
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}

/**
   A concurrent implementation of [`EventSubscriptionRelayer`]. With a given
   event subscription, the relayer puts each event relaying into a queue
   for executing them concurrently.

   Note that the implementation of this relayer is _concurrent_ but
   _not parallel_. This is because it uses [`StreamExt::for_each_concurrent`]
   for multiplexing between multiple concurrent executions. This means that
   if one of the event relayer is blocked synchronously, it may also block the
   execution of other relayers.

   Although there is the limitation of non-parallelism,
   [`ConcurrentEventSubscriptionRelayer`] is useful in use cases where parallel
   executions are _not_ possible, such as inside deterministic tests or inside
   single-threaded environments. In such cases, it would still be possible to
   have concurrent execution of event relaying.

   For support on both concurrent parallel relaying of events, use
   [`ParallelEventSubscriptionRelayer`].
*/
struct ConcurrentEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target, Runtime> EventSubscriptionRelayer<Relay, Target>
    for ConcurrentEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSubscribe,
{
    async fn relay_chain_event_subscription(
        relay: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        loop {
            if let Some(event_stream) = Runtime::subscribe(&event_subscription) {
                event_stream
                    .for_each_concurrent(None, |item| async move {
                        let (height, event) = item.as_ref();

                        // Ignore any relaying errors, as the relayer still needs to proceed
                        // relaying the next event regardless.
                        let _ = relay.relay_chain_event(&height, &event).await;
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}

/**
   A concurrent and parallel implementation of [`EventSubscriptionRelayer`].
   With a given event subscription, the relayer spawns a new background task
   for relaying the given event.

   This implementation requires the chain runtime to implement [`HasSpawner`]
   for spawning async tasks. Hence it may not be usable in single-threaded
   environments that do not support parallel tasks. In such cases,
   [`ConcurrentEventSubscriptionRelayer`] can be used for concurrent execution
   of event relaying multiplexed inside a single thread.
*/
struct ParallelEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target, Runtime> EventSubscriptionRelayer<Relay, Target>
    for ParallelEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target> + Clone,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSubscribe + HasSpawner,
{
    async fn relay_chain_event_subscription(
        relay: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        let runtime = Target::target_chain(relay).runtime();

        loop {
            if let Some(event_stream) = Runtime::subscribe(&event_subscription) {
                event_stream
                    .for_each_concurrent(None, |item| async move {
                        let relay = relay.clone();
                        let spawner = runtime.spawner();

                        spawner.spawn(async move {
                            let (height, event) = item.as_ref();

                            // Ignore any relaying errors, as the relayer still needs to proceed
                            // relaying the next event regardless.
                            let _ = relay.relay_chain_event(&height, &event).await;
                        });
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}
