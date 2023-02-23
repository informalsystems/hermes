use async_trait::async_trait;
use futures::stream::StreamExt;
use ibc_relayer_components::chain::traits::event_subscription::HasEventSubscription;
use ibc_relayer_components::relay::traits::auto_relayer::AutoRelayerWithTarget;
use ibc_relayer_components::relay::traits::event_relayer::CanRelayEvent;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::runtime::traits::spawn::{HasSpawner, Spawner};
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

                        let handle = spawner.spawn(async move {
                            let (height, event) = item;

                            // Ignore any relaying errors, as the relayer still needs to proceed
                            // relaying the next event regardless.
                            // TODO: log errors inside EventRelayer
                            let _ = relay.relay_chain_event(&height, &event).await;
                        });

                        handle.into_future().await;
                    })
                    .await;
            } else {
                return;
            }
        }
    }
}
