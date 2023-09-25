use core::future::Future;
use core::marker::PhantomData;
use core::pin::Pin;

use async_trait::async_trait;
use futures_util::stream::{self, StreamExt};

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::auto_relayer::{AutoRelayer, AutoRelayerWithTarget};
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

/// A concurrent bidirectional relay context that supports auto-relaying between two
/// targets, a `SourceTarget` and a `DestinationTarget`. It is composed of two
/// unidirectional relay contexts.
///
/// Note that the `InRelayer` parameter is constrained such that the two sub-relay
/// contexts must relay between the same two connected chains, the `SourceTarget`
/// chain and the `DestinationTarget` chain, except in different directions.
///
/// This relayer type aggregates the relay tasks bound for the source chain and the tasks
/// bound for the target chain, collects them into a single stream, and then relays the
/// stream of tasks in cooperative multi-tasking fashion, which is how it achieves
/// concurrency.
pub struct ConcurrentBidirectionalRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> AutoRelayer<Relay> for ConcurrentBidirectionalRelayer<InRelayer>
where
    Relay: HasRelayChains,
    InRelayer: AutoRelayerWithTarget<Relay, SourceTarget>,
    InRelayer: AutoRelayerWithTarget<Relay, DestinationTarget>,
{
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error> {
        let src_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            let _ =
                <InRelayer as AutoRelayerWithTarget<Relay, SourceTarget>>::auto_relay_with_target(
                    relay,
                )
                .await;
        });

        let dst_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            let _ = <InRelayer as AutoRelayerWithTarget<Relay, DestinationTarget>>::auto_relay_with_target(
                relay,
            )
            .await;
        });

        stream::iter([src_task, dst_task])
            .for_each_concurrent(None, |task| task)
            .await;

        Ok(())
    }
}
