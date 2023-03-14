use alloc::sync::Arc;
use core::pin::Pin;
use tendermint_rpc::client::CompatMode;

use async_trait::async_trait;
use futures::stream::{self, Stream, StreamExt, TryStreamExt};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::impls::subscription::closure::CanCreateClosureSubscription;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_components_extra::runtime::impls::subscription::multiplex::CanMultiplexSubscription;
use ibc_relayer_components_extra::runtime::traits::spawn::{HasSpawner, Spawner};
use ibc_relayer_types::core::ics02_client::height::Height;
use tendermint::abci::Event as AbciEvent;
use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};
use tendermint_rpc::query::Query;
use tendermint_rpc::{SubscriptionClient, WebSocketClient, WebSocketClientUrl};

use crate::base::error::{BaseError, Error};

pub trait CanCreateAbciEventSubscription: Async {
    fn new_abci_event_subscription(
        &self,
        chain_version: u64,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: Vec<Query>,
    ) -> Arc<dyn Subscription<Item = (Height, AbciEvent)>>;
}

impl<Runtime> CanCreateAbciEventSubscription for Runtime
where
    Runtime:
        CanCreateRpcEventStream + CanCreateClosureSubscription + CanMultiplexSubscription + Clone,
{
    fn new_abci_event_subscription(
        &self,
        chain_version: u64,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: Vec<Query>,
    ) -> Arc<dyn Subscription<Item = (Height, AbciEvent)>> {
        let base_subscription = {
            let runtime = self.clone();

            Runtime::new_closure_subscription(move || {
                let runtime = runtime.clone();
                let websocket_url = websocket_url.clone();
                let compat_mode = compat_mode.clone();
                let queries = queries.clone();

                Box::pin(async move {
                    // TODO: log error
                    let rpc_event_stream = runtime
                        .new_rpc_event_stream(websocket_url.clone(), compat_mode.clone(), &queries)
                        .await
                        .ok()?;

                    let abci_event_stream =
                        rpc_event_to_abci_event_stream(chain_version, rpc_event_stream);

                    Some(abci_event_stream)
                })
            })
        };

        let subscription = self.multiplex_subscription(base_subscription, |e| e);

        subscription
    }
}

pub fn rpc_event_to_abci_event_stream(
    chain_version: u64,
    rpc_event_stream: Pin<Box<dyn Stream<Item = RpcEvent> + Send + 'static>>,
) -> Pin<Box<dyn Stream<Item = (Height, AbciEvent)> + Send + 'static>> {
    let abci_event_stream = rpc_event_stream
        .filter_map(move |rpc_event| async move {
            match rpc_event.data {
                RpcEventData::Tx { tx_result } => {
                    // TODO: log error
                    let height = Height::new(chain_version, tx_result.height as u64).ok()?;

                    let events_with_height = tx_result
                        .result
                        .events
                        .into_iter()
                        .map(|event| (height, event))
                        .collect::<Vec<_>>();

                    Some(stream::iter(events_with_height))
                }
                _ => None,
            }
        })
        .flatten();

    Box::pin(abci_event_stream)
}

#[async_trait]
pub trait CanCreateRpcEventStream: Async {
    async fn new_rpc_event_stream(
        &self,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: &[Query],
    ) -> Result<Pin<Box<dyn Stream<Item = RpcEvent> + Send + 'static>>, Error>;
}

#[async_trait]
impl<Runtime> CanCreateRpcEventStream for Runtime
where
    Runtime: HasSpawner,
{
    async fn new_rpc_event_stream(
        &self,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: &[Query],
    ) -> Result<Pin<Box<dyn Stream<Item = RpcEvent> + Send + 'static>>, Error> {
        let builder = WebSocketClient::builder(websocket_url).compat_mode(compat_mode);

        let (client, driver) = builder.build().await.map_err(BaseError::tendermint_rpc)?;

        let spawner = self.spawner();
        spawner.spawn(async move {
            let _ = driver.run().await;
        });

        let subscriptions = stream::iter(queries.iter())
            .then(|query| async { client.subscribe(query.clone()).await })
            .try_collect::<Vec<_>>()
            .await
            .map_err(BaseError::tendermint_rpc)?;

        let stream = stream::select_all(subscriptions).filter_map(|event| async { event.ok() });

        Ok(Box::pin(stream))
    }
}
