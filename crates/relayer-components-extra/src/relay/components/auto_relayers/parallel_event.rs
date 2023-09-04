use async_trait::async_trait;
use futures_util::stream::StreamExt;
use ibc_relayer_components::chain::traits::event_subscription::HasEventSubscription;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::components::auto_relayer::AutoRelayerWithTarget;
use ibc_relayer_components::relay::traits::components::event_relayer::CanRelayEvent;
use ibc_relayer_components::relay::traits::logs::event::CanLogTargetEvent;
use ibc_relayer_components::relay::traits::logs::logger::CanLogRelay;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

pub struct ParallelEventSubscriptionRelayer;

#[async_trait]
impl<Relay, Target, Runtime> AutoRelayerWithTarget<Relay, Target>
    for ParallelEventSubscriptionRelayer
where
    Relay: Clone + CanRelayEvent<Target> + CanLogRelay + CanLogTargetEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime> + HasEventSubscription,
    Runtime: HasSpawner,
{
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error> {
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

                            let res = relay.relay_chain_event(&height, &event).await;

                            if let Err(e) = res {
                                relay.log_relay(
                                    Relay::Logger::LEVEL_ERROR,
                                    "error relaying chain event",
                                    |log| {
                                        log.field("event", Relay::log_target_event(&event))
                                            .debug("error", &e);
                                    },
                                )
                            }
                        });

                        handle.into_future().await;
                    })
                    .await;
            } else {
                return Ok(());
            }
        }
    }
}
