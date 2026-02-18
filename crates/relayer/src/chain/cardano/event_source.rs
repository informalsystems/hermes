//! Event source for Cardano chain
//!
//! Polls the Gateway for IBC events and broadcasts them to subscribers.

use std::sync::Arc;

use crossbeam_channel as channel;
use tokio::{
    runtime::Runtime as TokioRuntime,
    time::{sleep, Duration, Instant},
};
use tracing::{debug, error, error_span, trace};

use ibc_relayer_types::core::{ics02_client::height::Height, ics24_host::identifier::ChainId};

use crate::{
    chain::tracking::TrackingId,
    event::{bus::EventBus, source::Error, IbcEventWithHeight},
    telemetry,
};

use super::{event_parser, gateway_client::GatewayClient};

use crate::event::source::{EventBatch, EventSourceCmd, TxEventSourceCmd};

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Copy, Clone)]
enum Next {
    Continue,
    Abort,
}

/// An event source that polls the Cardano Gateway for IBC events
pub struct CardanoEventSource {
    /// Chain identifier
    chain_id: ChainId,

    /// Gateway client for querying events
    gateway_client: GatewayClient,

    /// Poll interval
    poll_interval: Duration,

    /// Event bus for broadcasting events
    event_bus: EventBus<Arc<Result<EventBatch>>>,

    /// Channel where to receive commands
    rx_cmd: channel::Receiver<EventSourceCmd>,

    /// Tokio runtime
    rt: Arc<TokioRuntime>,

    /// Last fetched block height
    last_fetched_height: Height,
}

impl CardanoEventSource {
    pub fn new(
        chain_id: ChainId,
        gateway_client: GatewayClient,
        poll_interval: Duration,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxEventSourceCmd)> {
        let event_bus = EventBus::new();
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let source = Self {
            rt,
            chain_id,
            gateway_client,
            poll_interval,
            event_bus,
            rx_cmd,
            // Start at a valid (non-zero) height; `run()` will immediately reset this
            // to the latest height if the gateway is reachable.
            last_fetched_height: Height::new(0, 1).map_err(|e| {
                Error::collect_events_failed(format!("Failed to create initial height: {}", e))
            })?,
        };

        Ok((source, TxEventSourceCmd::new(tx_cmd)))
    }

    pub fn run(mut self) {
        let _span = error_span!("event_source.cardano", chain.id = %self.chain_id).entered();

        debug!("starting Cardano event source");

        let rt = self.rt.clone();

        rt.block_on(async {
            // Initialize the latest fetched height
            if let Ok(latest_height) = self.fetch_latest_height().await {
                self.last_fetched_height = latest_height;
                debug!("initialized at height: {}", self.last_fetched_height);
            }

            // Continuously run the event loop
            loop {
                let before_step = Instant::now();

                match self.step().await {
                    Ok(Next::Abort) => break,

                    Ok(Next::Continue) => {
                        // Check if we need to wait before the next iteration
                        let delay = self.poll_interval.checked_sub(before_step.elapsed());

                        if let Some(delay_remaining) = delay {
                            sleep(delay_remaining).await;
                        }

                        continue;
                    }

                    Err(e) => {
                        error!("event source encountered an error: {e}");
                        // Wait before retrying
                        sleep(Duration::from_secs(5)).await;
                    }
                }
            }
        });

        debug!("shutting down Cardano event source");
    }

    async fn step(&mut self) -> Result<Next> {
        // Process any shutdown or subscription commands before we start doing any work
        if let Next::Abort = self.try_process_cmd() {
            return Ok(Next::Abort);
        }

        // Query Gateway for events since last height
        let response = self
            .gateway_client
            .query_events(self.last_fetched_height)
            .await
            .map_err(|e| {
                Error::collect_events_failed(format!("Failed to query Gateway events: {}", e))
            })?;

        let current_height = Height::new(0, response.current_height).map_err(|e| {
            Error::collect_events_failed(format!("Invalid height from Gateway: {}", e))
        })?;

        // Process events if we have new blocks
        if !response.events.is_empty() {
            trace!(
                "received {} block(s) of events from height {} to {}",
                response.events.len(),
                self.last_fetched_height,
                current_height
            );

            for block_events in response.events {
                let batch = self.process_block_events(block_events)?;

                // Check for commands before broadcasting
                if let Next::Abort = self.try_process_cmd() {
                    return Ok(Next::Abort);
                }

                if let Some(batch) = batch {
                    self.broadcast_batch(batch);
                }
            }

            // Update last fetched height
            self.last_fetched_height = current_height;
        } else {
            trace!(
                "no new events, current height: {}, last fetched: {}",
                current_height,
                self.last_fetched_height
            );
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

    /// Process events from a single block
    fn process_block_events(
        &self,
        block_events: super::generated::ibc::cardano::v1::BlockEvents,
    ) -> Result<Option<EventBatch>> {
        let height = Height::new(0, block_events.height)
            .map_err(|e| Error::collect_events_failed(format!("Invalid block height: {}", e)))?;

        if block_events.events.is_empty() {
            return Ok(None);
        }

        // Flatten all events from all ResponseDeliverTx items and convert to cardano Event type
        let gateway_events: Vec<_> = block_events
            .events
            .into_iter()
            .flat_map(|tx_result| {
                tx_result.events.into_iter().map(|core_event| {
                    // Convert ibc.core.types.v1.Event to ibc.cardano.v1.Event
                    super::generated::ibc::cardano::v1::Event {
                        r#type: core_event.r#type,
                        attributes: core_event
                            .event_attribute
                            .into_iter()
                            .map(|attr| super::generated::ibc::cardano::v1::EventAttribute {
                                key: attr.key,
                                value: attr.value,
                            })
                            .collect(),
                    }
                })
            })
            .collect();

        if gateway_events.is_empty() {
            return Ok(None);
        }

        // Parse Gateway events into IBC events
        let ibc_events = event_parser::parse_events(gateway_events, height)
            .map_err(|e| Error::collect_events_failed(format!("Failed to parse events: {}", e)))?;

        if ibc_events.is_empty() {
            return Ok(None);
        }

        // Convert to IbcEventWithHeight
        let events_with_height: Vec<IbcEventWithHeight> = ibc_events
            .into_iter()
            .map(|event| IbcEventWithHeight::new(event, height))
            .collect();

        debug!(
            chain = %self.chain_id,
            height = %height,
            count = events_with_height.len(),
            "parsed {} IBC events at height {}",
            events_with_height.len(),
            height
        );

        let batch = EventBatch {
            chain_id: self.chain_id.clone(),
            tracking_id: TrackingId::new_uuid(),
            height,
            events: events_with_height,
        };

        Ok(Some(batch))
    }

    /// Broadcast an event batch to all subscribers
    fn broadcast_batch(&mut self, batch: EventBatch) {
        telemetry!(ws_events, &batch.chain_id, batch.events.len() as u64);

        trace!(
            chain = %batch.chain_id,
            count = %batch.events.len(),
            height = %batch.height,
            "broadcasting batch of {} events at height {}",
            batch.events.len(),
            batch.height
        );

        self.event_bus.broadcast(Arc::new(Ok(batch)));
    }

    /// Fetch the current chain height from Gateway
    async fn fetch_latest_height(&self) -> Result<Height> {
        self.gateway_client
            .query_latest_height()
            .await
            .map_err(|e| {
                Error::collect_events_failed(format!("Failed to fetch latest height: {}", e))
            })
    }
}
