use core::future::Future;
use core::pin::Pin;

use async_trait::async_trait;
use futures_util::stream::{self, StreamExt};

use crate::relay::traits::components::auto_relayer::{AutoRelayer, CanAutoRelay};
use crate::relay::traits::two_way::HasTwoWayRelay;
use crate::std_prelude::*;

/// A concurrent two-way relay context that is composed of a `BiRelay` type that
/// can auto-relay between two connected targets.
///
/// As opposed to the `ParallelTwoWayAutoRelay` variant, this concurrent variant
/// runs in a single thread and achieves concurrency via cooperative multi-tasking.
pub struct ConcurrentTwoWayAutoRelay;

#[async_trait]
impl<BiRelay> AutoRelayer<BiRelay> for ConcurrentTwoWayAutoRelay
where
    BiRelay: HasTwoWayRelay,
    BiRelay::RelayAToB: CanAutoRelay,
    BiRelay::RelayBToA: CanAutoRelay,
{
    async fn auto_relay(birelay: &BiRelay) -> Result<(), BiRelay::Error> {
        let a_to_b_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            let _ = birelay.relay_a_to_b().auto_relay().await;
        });

        let b_to_a_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            let _ = birelay.relay_b_to_a().auto_relay().await;
        });

        stream::iter([a_to_b_task, b_to_a_task])
            .for_each_concurrent(None, |task| task)
            .await;

        Ok(())
    }
}
