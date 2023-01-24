use async_trait::async_trait;
use core::future::Future;
use core::marker::PhantomData;
use core::pin::Pin;
use futures::stream::{self, StreamExt};

use crate::base::relay::traits::auto_relayer::{AutoRelayer, AutoRelayerWithTarget};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct ConcurrentBidirectionalRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> AutoRelayer<Relay> for ConcurrentBidirectionalRelayer<InRelayer>
where
    Relay: HasRelayTypes,
    InRelayer: AutoRelayerWithTarget<Relay, SourceTarget>,
    InRelayer: AutoRelayerWithTarget<Relay, DestinationTarget>,
{
    async fn auto_relay(relay: &Relay) {
        let src_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            <InRelayer as AutoRelayerWithTarget<Relay, SourceTarget>>::auto_relay_with_target(
                relay,
            )
            .await;
        });

        let dst_task: Pin<Box<dyn Future<Output = ()> + Send>> = Box::pin(async move {
            <InRelayer as AutoRelayerWithTarget<Relay, DestinationTarget>>::auto_relay_with_target(
                relay,
            )
            .await;
        });

        stream::iter([src_task, dst_task])
            .for_each_concurrent(None, |task| task)
            .await;
    }
}
