use core::marker::PhantomData;

use async_trait::async_trait;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayer, AutoRelayerWithTarget};
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

/// A parallel variant of
/// [`ConcurrentBidirectionalRelayer`](ibc_relayer_components::relay::impls::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer)
/// that spawns two separate
/// tasks, each responsible for relaying for one of the targets. As such, it has an
/// additional `HasSpawner` constraint that the concurrent variant does not require.
pub struct ParallelBidirectionalRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer, Runtime> AutoRelayer<Relay> for ParallelBidirectionalRelayer<InRelayer>
where
    Relay: HasRelayChains + HasRuntime<Runtime = Runtime> + Clone,
    InRelayer: AutoRelayerWithTarget<Relay, SourceTarget>,
    InRelayer: AutoRelayerWithTarget<Relay, DestinationTarget>,
    Runtime: HasSpawner,
{
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error> {
        let src_relay = relay.clone();
        let dst_relay = relay.clone();
        let spawner = src_relay.runtime().spawner();

        let handle1 = spawner.spawn(async move {
            let _ = <InRelayer as AutoRelayerWithTarget<Relay, DestinationTarget>>::auto_relay_with_target(
                &dst_relay,
            )
            .await;
        });

        let handle2 = spawner.spawn(async move {
            let _ =
                <InRelayer as AutoRelayerWithTarget<Relay, SourceTarget>>::auto_relay_with_target(
                    &src_relay,
                )
                .await;
        });

        // Wait for handle1 and handle2 to finish.
        // Equivalent to Join.
        // TODO: Confirm with Soares
        handle1.into_future().await;
        handle2.into_future().await;

        Ok(())
    }
}
