use std::sync::Arc;

use crossbeam_channel as channel;
use tokio::{
    runtime::Runtime as TokioRuntime,
    time::{sleep, Duration, Instant},
};
use tracing::{debug, error, trace};

use tendermint::abci;
use tendermint::block::Height as BlockHeight;
use tendermint_rpc::{Client, HttpClient};

use ibc_relayer_types::{
    core::{
        ics02_client::{events::NewBlock, height::Height},
        ics24_host::identifier::ChainId,
    },
    events::IbcEvent,
};

use crate::{
    chain::{handle::Subscription, tracking::TrackingId},
    telemetry,
    util::retry::ConstantGrowth,
};

mod error;
pub use error::*;

use super::{bus::EventBus, IbcEventWithHeight};

pub type Result<T> = core::result::Result<T, Error>;

const QUERY_INTERVAL: Duration = Duration::from_secs(1);
const MAX_QUERY_INTERVAL: Duration = Duration::from_secs(5);

/// A batch of events from a chain at a specific height
#[derive(Clone, Debug)]
pub struct EventBatch {
    pub chain_id: ChainId,
    pub tracking_id: TrackingId,
    pub height: Height,
    pub events: Vec<IbcEventWithHeight>,
}

pub type EventSender = channel::Sender<Result<EventBatch>>;
pub type EventReceiver = channel::Receiver<Result<EventBatch>>;

#[derive(Clone, Debug)]
pub struct TxMonitorCmd(channel::Sender<MonitorCmd>);

impl TxMonitorCmd {
    pub fn shutdown(&self) -> Result<()> {
        self.0
            .send(MonitorCmd::Shutdown)
            .map_err(|_| Error::channel_send_failed())
    }

    pub fn subscribe(&self) -> Result<Subscription> {
        let (tx, rx) = crossbeam_channel::bounded(1);

        self.0
            .send(MonitorCmd::Subscribe(tx))
            .map_err(|_| Error::channel_send_failed())?;

        let subscription = rx.recv().map_err(|_| Error::channel_recv_failed())?;
        Ok(subscription)
    }
}

#[derive(Debug)]
pub enum MonitorCmd {
    Shutdown,
    Subscribe(channel::Sender<Subscription>),
}

pub struct EventMonitor {
    /// Chain identifier
    chain_id: ChainId,

    /// Latest block height
    latest_block_height: BlockHeight,

    /// RPC client
    rpc_client: HttpClient,

    /// Event bus for broadcasting events
    event_bus: EventBus<Arc<Result<EventBatch>>>,

    /// Channel where to receive commands
    rx_cmd: channel::Receiver<MonitorCmd>,

    /// Tokio runtime
    rt: Arc<TokioRuntime>,
}

impl EventMonitor {
    pub fn new(
        chain_id: ChainId,
        rpc_client: HttpClient,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxMonitorCmd)> {
        let event_bus = EventBus::new();
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let monitor = Self {
            rt,
            chain_id,
            latest_block_height: BlockHeight::from(0_u32),
            rpc_client,
            event_bus,
            rx_cmd,
        };

        Ok((monitor, TxMonitorCmd(tx_cmd)))
    }

    pub fn run(mut self) {
        debug!("starting event monitor");

        let rt = self.rt.clone();

        rt.block_on(async {
            let mut backoff = monitor_backoff();

            // Continuously run the event loop, so that when it aborts
            // because of WebSocket client restart, we pick up the work again.
            loop {
                let before_step = Instant::now();

                match self.step().await {
                    Ok(Next::Abort) => break,

                    Ok(Next::Continue) => {
                        // Reset the backoff
                        backoff = monitor_backoff();

                        // Check if we need to wait some more before the next iteration.
                        let delay = QUERY_INTERVAL.checked_sub(before_step.elapsed());
                        if let Some(delay_remaining) = delay {
                            sleep(delay_remaining).await;
                        }

                        continue;
                    }

                    Err(e) => {
                        error!("event monitor encountered an error: {e}");

                        // Let's backoff the little bit to give the chain some time to recover.
                        let delay = backoff.next().expect("backoff is an infinite iterator");

                        error!("retrying in {delay:?}...");
                        sleep(delay).await;
                    }
                }
            }
        });

        debug!("shutting down event monitor");
    }

    async fn step(&mut self) -> Result<Next> {
        // Process any shutdown or subscription commands before we start doing any work
        if let Ok(cmd) = self.rx_cmd.try_recv() {
            match cmd {
                MonitorCmd::Shutdown => return Ok(Next::Abort),
                MonitorCmd::Subscribe(tx) => {
                    if let Err(e) = tx.send(self.event_bus.subscribe()) {
                        error!("failed to send back subscription: {e}");
                    }
                }
            }
        }

        let latest_height = self
            .rpc_client
            .status()
            .await
            .map_err(Error::rpc)?
            .sync_info
            .latest_block_height;

        let batch = if latest_height > self.latest_block_height {
            trace!(
                "latest height ({latest_height}) > latest block height ({})",
                self.latest_block_height
            );

            self.latest_block_height = latest_height;

            let result = collect_events(&self.rpc_client, &self.chain_id, latest_height).await;

            result.unwrap_or_else(|e| {
                error!("failed to collect events: {e}");
                None
            })
        } else {
            trace!(
                "latest height ({latest_height}) <= latest block height ({})",
                self.latest_block_height
            );

            None
        };

        // Before handling the batch, check if there are any pending shutdown or subscribe commands.
        if let Ok(cmd) = self.rx_cmd.try_recv() {
            match cmd {
                MonitorCmd::Shutdown => return Ok(Next::Abort),
                MonitorCmd::Subscribe(tx) => {
                    if let Err(e) = tx.send(self.event_bus.subscribe()) {
                        error!("failed to send back subscription: {e}");
                    }
                }
            }
        }

        if let Some(batch) = batch {
            self.broadcast_batch(batch);
        }

        Ok(Next::Continue)
    }

    /// Collect the IBC events from the subscriptions
    fn broadcast_batch(&mut self, batch: EventBatch) {
        telemetry!(ws_events, &batch.chain_id, batch.events.len() as u64);
        self.event_bus.broadcast(Arc::new(Ok(batch)));
    }
}

fn monitor_backoff() -> impl Iterator<Item = Duration> {
    ConstantGrowth::new(QUERY_INTERVAL, Duration::from_secs(1))
        .clamp(MAX_QUERY_INTERVAL, usize::MAX)
}

fn dedupe(events: Vec<abci::Event>) -> Vec<abci::Event> {
    use itertools::Itertools;
    use std::hash::{Hash, Hasher};

    #[derive(Clone, PartialEq, Eq)]
    struct HashEvent(abci::Event);

    impl Hash for HashEvent {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.kind.hash(state);
            for attr in &self.0.attributes {
                attr.key.hash(state);
                attr.value.hash(state);
                attr.index.hash(state);
            }
        }
    }

    events
        .into_iter()
        .map(HashEvent)
        .unique()
        .map(|e| e.0)
        .collect()
}

/// Collect the IBC events from an RPC event
async fn collect_events(
    rpc_client: &HttpClient,
    chain_id: &ChainId,
    latest_block_height: BlockHeight,
) -> Result<Option<EventBatch>> {
    use crate::event::rpc::get_all_events;

    let abci_events = fetch_all_events(rpc_client, latest_block_height)
        .await
        .map(dedupe)?;

    let height = Height::from_tm(latest_block_height, chain_id);
    let new_block_event =
        IbcEventWithHeight::new(IbcEvent::NewBlock(NewBlock::new(height)), height);

    let mut events = vec![new_block_event];
    let mut block_events = get_all_events(chain_id, height, &abci_events).unwrap_or_default();

    events.append(&mut block_events);

    Ok(Some(EventBatch {
        chain_id: chain_id.clone(),
        tracking_id: TrackingId::new_uuid(),
        height,
        events,
    }))
}

async fn fetch_all_events(
    rpc_client: &HttpClient,
    height: BlockHeight,
) -> Result<Vec<abci::Event>> {
    let mut response = rpc_client.block_results(height).await.map_err(Error::rpc)?;
    let mut events = vec![];

    if let Some(begin_block_events) = &mut response.begin_block_events {
        events.append(begin_block_events);
    }

    if let Some(txs_results) = &mut response.txs_results {
        for tx_result in txs_results {
            events.append(&mut tx_result.events);
        }
    }

    if let Some(end_block_events) = &mut response.end_block_events {
        events.append(end_block_events);
    }

    Ok(events)
}

pub enum Next {
    Abort,
    Continue,
}
