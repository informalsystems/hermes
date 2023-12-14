pub mod rpc;
pub mod websocket;

use std::{
    sync::Arc,
    time::Duration,
};

use crossbeam_channel as channel;
use futures::Stream;
use ibc_relayer_types::core::{
    ics02_client::height::Height,
    ics24_host::identifier::ChainId,
};
use tendermint_rpc::{
    client::CompatMode,
    event::Event as RpcEvent,
    Error as RpcError,
    HttpClient,
    WebSocketClientUrl,
};
use tokio::runtime::Runtime as TokioRuntime;

pub use super::error::{
    Error,
    ErrorDetail,
};
use super::IbcEventWithHeight;
use crate::chain::{
    handle::Subscription,
    tracking::TrackingId,
};

pub type Result<T> = core::result::Result<T, Error>;

pub enum EventSource {
    WebSocket(websocket::EventSource),
    Rpc(rpc::EventSource),
}

impl EventSource {
    pub fn websocket(
        chain_id: ChainId,
        ws_url: WebSocketClientUrl,
        rpc_compat: CompatMode,
        batch_delay: Duration,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxEventSourceCmd)> {
        let (mut source, tx) =
            websocket::EventSource::new(chain_id, ws_url, rpc_compat, batch_delay, rt)?;

        source.init_subscriptions()?;

        Ok((Self::WebSocket(source), tx))
    }

    pub fn rpc(
        chain_id: ChainId,
        rpc_client: HttpClient,
        poll_interval: Duration,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxEventSourceCmd)> {
        let (source, tx) = rpc::EventSource::new(chain_id, rpc_client, poll_interval, rt)?;
        Ok((Self::Rpc(source), tx))
    }

    pub fn run(self) {
        match self {
            Self::WebSocket(source) => source.run(),
            Self::Rpc(source) => source.run(),
        }
    }
}

/// A batch of events from a chain at a specific height
#[derive(Clone, Debug)]
pub struct EventBatch {
    pub chain_id: ChainId,
    pub tracking_id: TrackingId,
    pub height: Height,
    pub events: Vec<IbcEventWithHeight>,
}

type SubscriptionResult = core::result::Result<RpcEvent, RpcError>;
type SubscriptionStream = dyn Stream<Item = SubscriptionResult> + Send + Sync + Unpin;

pub type EventSender = channel::Sender<Result<EventBatch>>;
pub type EventReceiver = channel::Receiver<Result<EventBatch>>;

#[derive(Clone, Debug)]
pub struct TxEventSourceCmd(channel::Sender<EventSourceCmd>);

impl TxEventSourceCmd {
    pub fn shutdown(&self) -> Result<()> {
        self.0
            .send(EventSourceCmd::Shutdown)
            .map_err(|_| Error::channel_send_failed())
    }

    pub fn subscribe(&self) -> Result<Subscription> {
        let (tx, rx) = crossbeam_channel::bounded(1);

        self.0
            .send(EventSourceCmd::Subscribe(tx))
            .map_err(|_| Error::channel_send_failed())?;

        let subscription = rx.recv().map_err(|_| Error::channel_recv_failed())?;
        Ok(subscription)
    }
}

#[derive(Debug)]
pub enum EventSourceCmd {
    Shutdown,
    Subscribe(channel::Sender<Subscription>),
}

// TODO: These are SDK specific, should be eventually moved.
pub mod queries {
    use tendermint_rpc::query::{
        EventType,
        Query,
    };

    pub fn all() -> Vec<Query> {
        // Note: Tendermint-go supports max 5 query specifiers!
        vec![
            new_block(),
            ibc_client(),
            ibc_connection(),
            ibc_channel(),
            ibc_query(),
            // This will be needed when we send misbehavior evidence to full node
            // Query::eq("message.module", "evidence"),
        ]
    }

    pub fn new_block() -> Query {
        Query::from(EventType::NewBlock)
    }

    pub fn ibc_client() -> Query {
        Query::eq("message.module", "ibc_client")
    }

    pub fn ibc_connection() -> Query {
        Query::eq("message.module", "ibc_connection")
    }

    pub fn ibc_channel() -> Query {
        Query::eq("message.module", "ibc_channel")
    }

    pub fn ibc_query() -> Query {
        Query::eq("message.module", "interchainquery")
    }
}
