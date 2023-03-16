use alloc::sync::Arc;
use core::pin::Pin;
use tendermint_rpc::client::CompatMode;
use tracing::error;

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

/**
   Creates a new ABCI event subscription that automatically reconnects.

   Note: The returned event stream may contain duplicate events, depending
   on the input `queries` parameter.
*/
pub trait CanCreateAbciEventSubscription: Async {
    fn new_abci_event_subscription(
        &self,
        chain_version: u64,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: Vec<Query>,
    ) -> Arc<dyn Subscription<Item = (Height, Arc<AbciEvent>)>>;
}

impl<Runtime> CanCreateAbciEventSubscription for Runtime
where
    Runtime:
        CanCreateAbciEventStream + CanCreateClosureSubscription + CanMultiplexSubscription + Clone,
{
    fn new_abci_event_subscription(
        &self,
        chain_version: u64,
        websocket_url: WebSocketClientUrl,
        compat_mode: CompatMode,
        queries: Vec<Query>,
    ) -> Arc<dyn Subscription<Item = (Height, Arc<AbciEvent>)>> {
        let base_subscription = {
            let runtime = self.clone();

            Runtime::new_closure_subscription(move || {
                let runtime = runtime.clone();
                let websocket_url = websocket_url.clone();
                let queries = queries.clone();

                Box::pin(async move {
                    let stream_result = runtime
                        .new_abci_event_stream(
                            chain_version,
                            &websocket_url,
                            &compat_mode,
                            &queries,
                        )
                        .await;

                    match stream_result {
                        Ok(event_stream) => Some(event_stream),
                        Err(e) => {
                            error!(
                                error = "failed to create new ABCI event stream. terminating subscription",
                                details = %e,
                                websocket_url = %websocket_url,
                            );

                            None
                        }
                    }
                })
            })
        };

        let subscription = self.multiplex_subscription(base_subscription, |e| e);

        subscription
    }
}

#[async_trait]
pub trait CanCreateAbciEventStream: Async {
    async fn new_abci_event_stream(
        &self,
        chain_version: u64,
        websocket_url: &WebSocketClientUrl,
        compat_mode: &CompatMode,
        queries: &[Query],
    ) -> Result<Pin<Box<dyn Stream<Item = (Height, Arc<AbciEvent>)> + Send + 'static>>, Error>;
}

#[async_trait]
impl<Runtime> CanCreateAbciEventStream for Runtime
where
    Runtime: HasSpawner,
{
    async fn new_abci_event_stream(
        &self,
        chain_version: u64,
        websocket_url: &WebSocketClientUrl,
        compat_mode: &CompatMode,
        queries: &[Query],
    ) -> Result<Pin<Box<dyn Stream<Item = (Height, Arc<AbciEvent>)> + Send + 'static>>, Error> {
        let builder = WebSocketClient::builder(websocket_url.clone()).compat_mode(*compat_mode);

        let (client, driver) = builder.build().await.map_err(BaseError::tendermint_rpc)?;

        let spawner = self.spawner();
        spawner.spawn(async move {
            let _ = driver.run().await;
        });

        let event_stream =
            new_abci_event_stream_with_queries(chain_version, &client, queries).await?;

        Ok(event_stream)
    }
}

async fn new_abci_event_stream_with_queries(
    chain_version: u64,
    websocket_client: &WebSocketClient,
    queries: &[Query],
) -> Result<Pin<Box<dyn Stream<Item = (Height, Arc<AbciEvent>)> + Send + 'static>>, Error> {
    let event_streams = stream::iter(queries)
        .then(|query| new_abci_event_stream_with_query(chain_version, websocket_client, query))
        .try_collect::<Vec<_>>()
        .await?;

    let event_stream = stream::iter(event_streams).flatten();

    Ok(Box::pin(event_stream))
}

async fn new_abci_event_stream_with_query(
    chain_version: u64,
    websocket_client: &WebSocketClient,
    query: &Query,
) -> Result<Pin<Box<dyn Stream<Item = (Height, Arc<AbciEvent>)> + Send + 'static>>, Error> {
    let rpc_stream = new_rpc_event_stream(websocket_client, query).await?;

    let abci_stream = rpc_stream
        .filter_map(move |rpc_event| async move {
            match rpc_event.data {
                RpcEventData::Tx { tx_result } => {
                    // TODO: log error
                    let height = Height::new(chain_version, tx_result.height as u64).ok()?;

                    let events_with_height = tx_result
                        .result
                        .events
                        .into_iter()
                        .map(|event| (height, Arc::new(event)))
                        .collect::<Vec<_>>();

                    Some(stream::iter(events_with_height))
                }
                _ => None,
            }
        })
        .flatten();

    Ok(Box::pin(abci_stream))
}

async fn new_rpc_event_stream(
    websocket_client: &WebSocketClient,
    query: &Query,
) -> Result<Pin<Box<dyn Stream<Item = RpcEvent> + Send + 'static>>, Error> {
    let subscription = websocket_client
        .subscribe(query.clone())
        .await
        .map_err(BaseError::tendermint_rpc)?;

    let stream = subscription.filter_map(|event| async { event.ok() });

    Ok(Box::pin(stream))
}
