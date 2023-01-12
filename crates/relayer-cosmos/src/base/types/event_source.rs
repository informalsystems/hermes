use core::pin::Pin;
use futures::stream::{self, Stream, StreamExt, TryStreamExt};
use ibc_relayer::event::monitor::queries;
use tendermint::abci::Event;
use tendermint_rpc::event::EventData;
use tendermint_rpc::{SubscriptionClient, WebSocketClient, WebSocketClientDriver};
use tokio::runtime::Runtime;
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver};

use crate::base::error::Error;

pub struct CosmosEventSource {
    pub stream: Pin<Box<dyn Stream<Item = Event>>>,
}

impl CosmosEventSource {}

pub async fn subscribe_events_with_client(
    websocket_address: &str,
    runtime: &Runtime,
    client: &WebSocketClient,
) -> Result<CosmosEventSource, Error> {
    // let (client, driver) = WebSocketClient::new(websocket_address).await
    //     .map_err(Error::tendermint_rpc)?;

    // runtime.spawn(async move {
    //     // TODO: propagate error to handle resubscription
    //     let _ = driver.run().await;
    // });

    let subscriptions = stream::iter(queries::all())
        .filter_map(|query| async { Some(client.subscribe(query).await) })
        .try_collect::<Vec<_>>()
        .await
        .map_err(Error::tendermint_rpc)?;

    let event_stream = stream::select_all(subscriptions).flat_map(|res| {
        match res {
            Ok(event) => match event.data {
                EventData::Tx { tx_result } => stream::iter(tx_result.result.events),
                _ => stream::iter(Vec::new()),
            },
            Err(_) => {
                // We are not interested in errors other than disconnection
                stream::iter(Vec::new())
            }
        }
    });

    Ok(CosmosEventSource {
        stream: Box::pin(event_stream),
    })
}
