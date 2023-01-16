use async_trait::async_trait;
use futures::stream::StreamExt;

use crate::base::chain::types::aliases::{EventSubscription, Runtime};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::event_relayer::CanRelayEvent;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::subscription::{CanSubscribe, HasSubscriptionType};
use crate::std_prelude::*;

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
                event_stream
                    .for_each(|item| async move {
                        let (height, event) = item.as_ref();
                        let _ = relay.relay_chain_event(&height, &event).await;
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}

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
                        let _ = relay.relay_chain_event(&height, &event).await;
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}
