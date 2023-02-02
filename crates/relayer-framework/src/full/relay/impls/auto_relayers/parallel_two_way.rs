use async_trait::async_trait;

use crate::base::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

pub struct ParallelTwoWayAutoRelay;

#[async_trait]
impl<BiRelay, Runtime> AutoRelayer<BiRelay> for ParallelTwoWayAutoRelay
where
    BiRelay: HasTwoWayRelay,
    Runtime: HasSpawner,
    BiRelay::RelayAToB: CanAutoRelay + HasRuntime<Runtime = Runtime> + Clone,
    BiRelay::RelayBToA: CanAutoRelay + Clone,
{
    async fn auto_relay(birelay: &BiRelay) {
        let relay_a_to_b = birelay.relay_a_to_b().clone();
        let relay_b_to_a = birelay.relay_b_to_a().clone();
        let spawner = relay_a_to_b.runtime().spawner();

        let handle1 = spawner.spawn(async move {
            BiRelay::RelayAToB::auto_relay(&relay_a_to_b).await;
        });

        let handle2 = spawner.spawn(async move {
            BiRelay::RelayBToA::auto_relay(&relay_b_to_a).await;
        });

        handle1.into_future().await;
        handle2.into_future().await;
    }
}
