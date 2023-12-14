pub mod extract;

use std::sync::Arc;

use crossbeam_channel as channel;
use ibc_relayer_types::{
    core::{
        ics02_client::{
            events::NewBlock,
            height::Height,
        },
        ics24_host::identifier::ChainId,
    },
    events::IbcEvent,
};
use tendermint::{
    abci,
    block::Height as BlockHeight,
};
use tendermint_rpc::{
    Client,
    HttpClient,
};
use tokio::{
    runtime::Runtime as TokioRuntime,
    time::{
        sleep,
        Duration,
        Instant,
    },
};
use tracing::{
    debug,
    error,
    error_span,
    trace,
};

use self::extract::extract_events;
use super::{
    EventBatch,
    EventSourceCmd,
    TxEventSourceCmd,
};
use crate::{
    chain::tracking::TrackingId,
    event::{
        bus::EventBus,
        source::Error,
        IbcEventWithHeight,
    },
    telemetry,
    util::retry::ConstantGrowth,
};

pub type Result<T> = core::result::Result<T, Error>;

/// An RPC endpoint that serves as a source of events for a given chain.
pub struct EventSource {
    /// Chain identifier
    chain_id: ChainId,

    /// RPC client
    rpc_client: HttpClient,

    /// Poll interval
    poll_interval: Duration,

    /// Event bus for broadcasting events
    event_bus: EventBus<Arc<Result<EventBatch>>>,

    /// Channel where to receive commands
    rx_cmd: channel::Receiver<EventSourceCmd>,

    /// Tokio runtime
    rt: Arc<TokioRuntime>,

    /// Last fetched block height
    last_fetched_height: BlockHeight,
}

impl EventSource {
    pub fn new(
        chain_id: ChainId,
        rpc_client: HttpClient,
        poll_interval: Duration,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxEventSourceCmd)> {
        let event_bus = EventBus::new();
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let source = Self {
            rt,
            chain_id,
            rpc_client,
            poll_interval,
            event_bus,
            rx_cmd,
            last_fetched_height: BlockHeight::from(0_u32),
        };

        Ok((source, TxEventSourceCmd(tx_cmd)))
    }

    pub fn run(mut self) {
        let _span = error_span!("event_source.rpc", chain.id = %self.chain_id).entered();

        debug!("collecting events");

        let rt = self.rt.clone();

        rt.block_on(async {
            let mut backoff = poll_backoff(self.poll_interval);

            // Initialize the latest fetched height
            if let Ok(latest_height) = latest_height(&self.rpc_client).await {
                self.last_fetched_height = latest_height;
            }

            // Continuously run the event loop, so that when it aborts
            // because of WebSocket client restart, we pick up the work again.
            loop {
                let before_step = Instant::now();

                match self.step().await {
                    Ok(Next::Abort) => break,

                    Ok(Next::Continue) => {
                        // Reset the backoff
                        backoff = poll_backoff(self.poll_interval);

                        // Check if we need to wait some more before the next iteration.
                        let delay = self.poll_interval.checked_sub(before_step.elapsed());

                        if let Some(delay_remaining) = delay {
                            sleep(delay_remaining).await;
                        }

                        continue;
                    }

                    Err(e) => {
                        error!("event source encountered an error: {e}");

                        // Let's backoff the little bit to give the chain some time to recover.
                        let delay = backoff.next().expect("backoff is an infinite iterator");

                        error!("retrying in {delay:?}...");
                        sleep(delay).await;
                    }
                }
            }
        });

        debug!("shutting down event source");
    }

    async fn step(&mut self) -> Result<Next> {
        // Process any shutdown or subscription commands before we start doing any work
        if let Next::Abort = self.try_process_cmd() {
            return Ok(Next::Abort);
        }

        let latest_height = latest_height(&self.rpc_client).await?;

        let batches = if latest_height > self.last_fetched_height {
            trace!(
                "latest height ({latest_height}) > latest fetched height ({})",
                self.last_fetched_height
            );

            self.fetch_batches(latest_height).await.map(Some)?
        } else {
            trace!(
                "latest height ({latest_height}) <= latest fetched height ({})",
                self.last_fetched_height
            );

            None
        };

        // Before handling the batch, check if there are any pending shutdown or subscribe commands.
        //
        // This avoids having the supervisor process an event batch after the event source has been shutdown.
        //
        // It also allows subscribers to receive the latest event batch even if they
        // subscribe while the batch being fetched.
        if let Next::Abort = self.try_process_cmd() {
            return Ok(Next::Abort);
        }

        for batch in batches.unwrap_or_default() {
            self.broadcast_batch(batch);
        }

        Ok(Next::Continue)
    }

    /// Process any pending commands, if any.
    fn try_process_cmd(&mut self) -> Next {
        if let Ok(cmd) = self.rx_cmd.try_recv() {
            match cmd {
                EventSourceCmd::Shutdown => return Next::Abort,

                EventSourceCmd::Subscribe(tx) => {
                    if let Err(e) = tx.send(self.event_bus.subscribe()) {
                        error!("failed to send back subscription: {e}");
                    }
                }
            }
        }

        Next::Continue
    }

    async fn fetch_batches(&mut self, latest_height: BlockHeight) -> Result<Vec<EventBatch>> {
        let start_height = self.last_fetched_height.increment();

        trace!("fetching blocks from {start_height} to {latest_height}");

        let heights = HeightRangeInclusive::new(start_height, latest_height);
        let mut batches = Vec::with_capacity(heights.len());

        for height in heights {
            trace!("collecting events at height {height}");

            let result = collect_events(&self.rpc_client, &self.chain_id, height).await;

            match result {
                Ok(batch) => {
                    self.last_fetched_height = height;

                    if let Some(batch) = batch {
                        batches.push(batch);
                    }
                }
                Err(e) => {
                    error!(%height, "failed to collect events: {e}");
                    break;
                }
            }
        }

        Ok(batches)
    }

    /// Collect the IBC events from the subscriptions
    fn broadcast_batch(&mut self, batch: EventBatch) {
        telemetry!(ws_events, &batch.chain_id, batch.events.len() as u64);

        trace!(
            chain = %batch.chain_id,
            count = %batch.events.len(),
            height = %batch.height,
            "broadcasting batch of {} events",
            batch.events.len()
        );

        self.event_bus.broadcast(Arc::new(Ok(batch)));
    }
}

fn poll_backoff(poll_interval: Duration) -> impl Iterator<Item = Duration> {
    ConstantGrowth::new(poll_interval, Duration::from_millis(500))
        .clamp(poll_interval * 5, usize::MAX)
}

fn dedupe(events: Vec<abci::Event>) -> Vec<abci::Event> {
    use std::hash::{
        Hash,
        Hasher,
    };

    use itertools::Itertools;

    #[derive(Clone)]
    struct HashEvent(abci::Event);

    impl PartialEq for HashEvent {
        fn eq(&self, other: &Self) -> bool {
            // NOTE: We don't compare on the index because it is not deterministic
            // NOTE: We need to check the length of the attributes in order
            // to not miss any attribute
            self.0.kind == other.0.kind
                && self.0.attributes.len() == other.0.attributes.len()
                && self
                    .0
                    .attributes
                    .iter()
                    .zip(other.0.attributes.iter())
                    .all(|(a, b)| a.key == b.key && a.value == b.value)
        }
    }

    impl Eq for HashEvent {}

    impl Hash for HashEvent {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.kind.hash(state);

            for attr in &self.0.attributes {
                // NOTE: We don't hash the index because it is not deterministic
                attr.key.hash(state);
                attr.value.hash(state);
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
    let abci_events = fetch_all_events(rpc_client, latest_block_height).await?;
    trace!("Found {} ABCI events before dedupe", abci_events.len());

    let abci_events = dedupe(abci_events);
    trace!("Found {} ABCI events after dedupe", abci_events.len());

    let height = Height::from_tm(latest_block_height, chain_id);
    let new_block_event =
        IbcEventWithHeight::new(IbcEvent::NewBlock(NewBlock::new(height)), height);

    let mut block_events = extract_events(chain_id, height, &abci_events).unwrap_or_default();
    let mut events = Vec::with_capacity(block_events.len() + 1);
    events.push(new_block_event);
    events.append(&mut block_events);

    trace!(
        "collected {events_len} events at height {height}: {events:#?}",
        events_len = events.len(),
        height = height,
    );

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
            if tx_result.code != abci::Code::Ok {
                // Transaction failed, skip it
                continue;
            }

            events.append(&mut tx_result.events);
        }
    }

    if let Some(end_block_events) = &mut response.end_block_events {
        events.append(end_block_events);
    }

    Ok(events)
}

async fn latest_height(rpc_client: &HttpClient) -> Result<BlockHeight> {
    rpc_client
        .abci_info()
        .await
        .map(|status| status.last_block_height)
        .map_err(Error::rpc)
}

pub enum Next {
    Abort,
    Continue,
}

pub struct HeightRangeInclusive {
    current: BlockHeight,
    end: BlockHeight,
}

impl HeightRangeInclusive {
    pub fn new(start: BlockHeight, end: BlockHeight) -> Self {
        Self {
            current: start,
            end,
        }
    }
}

impl Iterator for HeightRangeInclusive {
    type Item = BlockHeight;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current > self.end {
            None
        } else {
            let current = self.current;
            self.current = self.current.increment();
            Some(current)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end.value() - self.current.value() + 1;
        (size as usize, Some(size as usize))
    }
}

impl ExactSizeIterator for HeightRangeInclusive {}
