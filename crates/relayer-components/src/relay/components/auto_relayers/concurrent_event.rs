use async_trait::async_trait;
use futures_util::stream::StreamExt;

use crate::chain::traits::event_subscription::HasEventSubscription;
use crate::relay::traits::components::auto_relayer::AutoRelayerWithTarget;
use crate::relay::traits::components::event_relayer::CanRelayEvent;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

/// A one-way auto-relayer type that is responsible for listening for a
/// particular event subscription and relaying messages to a target
/// chain in response to those events in a concurrent fashion.
pub struct ConcurrentEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target> AutoRelayerWithTarget<Relay, Target> for ConcurrentEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventSubscription,
{
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error> {
        let subscription = Target::target_chain(relay).event_subscription();

        loop {
            if let Some(event_stream) = subscription.subscribe().await {
                event_stream
                    .for_each_concurrent(None, |item| async move {
                        let (height, event) = item;

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
