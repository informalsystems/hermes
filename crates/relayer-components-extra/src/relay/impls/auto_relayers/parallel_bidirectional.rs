use core::marker::PhantomData;

use async_trait::async_trait;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayer, AutoRelayerWithTarget};
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::relay::traits::types::HasRelayTypes;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

pub struct ParallelBidirectionalRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer, Runtime> AutoRelayer<Relay> for ParallelBidirectionalRelayer<InRelayer>
where
    Relay: HasRelayTypes + HasRuntime<Runtime = Runtime> + Clone,
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

        handle1.into_future().await;
        handle2.into_future().await;

        Ok(())
    }
}
