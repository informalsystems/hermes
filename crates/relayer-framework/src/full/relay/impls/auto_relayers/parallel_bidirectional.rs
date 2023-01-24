use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::relay::traits::auto_relayer::{AutoRelayer, AutoRelayerWithTarget};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
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
    async fn auto_relay(relay: &Relay) {
        let src_relay = relay.clone();
        let dst_relay = relay.clone();
        let spawner = src_relay.runtime().spawner();

        spawner.spawn(async move {
            <InRelayer as AutoRelayerWithTarget<Relay, DestinationTarget>>::auto_relay_with_target(
                &dst_relay,
            )
            .await;
        });

        spawner.spawn(async move {
            <InRelayer as AutoRelayerWithTarget<Relay, SourceTarget>>::auto_relay_with_target(
                &src_relay,
            )
            .await
        });

        // TODO: implement JoinHandle in HasSpawner
    }
}
