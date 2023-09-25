use async_trait::async_trait;
use futures_util::stream::StreamExt;

use crate::chain::traits::event_subscription::HasEventSubscription;
use crate::relay::traits::components::auto_relayer::AutoRelayerWithTarget;
use crate::relay::traits::components::event_relayer::CanRelayEvent;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct SequentialEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target> AutoRelayerWithTarget<Relay, Target> for SequentialEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventSubscription,
{
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error> {
        let subscription = Target::target_chain(relay).event_subscription();

        loop {
            if let Some(event_stream) = subscription.subscribe().await {
                // Use [`StreamExt::foreach`] to process the events sequentially.
                event_stream
                    .for_each(|item| async move {
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
