use async_trait::async_trait;
use futures::stream::StreamExt;

use crate::base::chain::traits::event_subscription::HasEventSubscription;
use crate::base::relay::traits::auto_relayer::AutoRelayerWithTarget;
use crate::base::relay::traits::event_relayer::CanRelayEvent;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

pub struct ParallelEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target, Runtime> AutoRelayerWithTarget<Relay, Target>
    for ParallelEventSubscriptionRelayer
where
    Relay: CanRelayEvent<Target> + Clone,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime> + HasEventSubscription,
    Runtime: HasSpawner,
{
    async fn auto_relay_with_target(relay: &Relay) {
        let chain = Target::target_chain(relay);
        let runtime = chain.runtime();
        let subscription = chain.event_subscription();

        loop {
            if let Some(event_stream) = subscription.subscribe().await {
                event_stream
                    .for_each_concurrent(None, |item| async move {
                        let relay = relay.clone();
                        let spawner = runtime.spawner();

                        spawner.spawn(async move {
                            let (height, event) = item;

                            // Ignore any relaying errors, as the relayer still needs to proceed
                            // relaying the next event regardless.
                            let _ = relay.relay_chain_event(&height, &event).await;
                        });
                    })
                    .await;
            } else {
                return;
            }
        }
    }
}
