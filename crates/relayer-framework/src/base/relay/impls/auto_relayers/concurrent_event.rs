use async_trait::async_trait;
use core::marker::PhantomData;
use futures::stream::StreamExt;

use crate::base::chain::traits::event_subscription::HasEventSubscription;
use crate::base::relay::traits::auto_relayer::AutoRelayer;
use crate::base::relay::traits::event_relayer::CanRelayEvent;
use crate::base::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

struct ConcurrentEventSubscriptionRelayer<Target>(pub PhantomData<Target>);

#[async_trait]
impl<Relay, Target> AutoRelayer<Relay> for ConcurrentEventSubscriptionRelayer<Target>
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventSubscription,
{
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error> {
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
