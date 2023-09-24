use super::{error::Error, source::EventBatch, IbcEventWithHeight};
use crate::chain::{
    handle::Subscription,
    near::{
        contract::NearIbcContract,
        error::NearError,
        rpc::{client::NearRpcClient, tool::convert_ibc_event_to_hermes_ibc_event},
    },
    tracking::TrackingId,
};
use alloc::sync::Arc;
use crossbeam_channel as channel;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::{
    core::ics02_client::height::Height, core::ics24_host::identifier::ChainId,
};
use near_primitives::types::AccountId;
use serde_json::json;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::{error, info, instrument, warn};

pub type Result<T> = core::result::Result<T, Error>;

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
    Subscribe(crossbeam_channel::Sender<Subscription>),
}

pub enum Next {
    Abort,
    Continue,
}

/// Connect to a Tendermint node, subscribe to a set of queries,
/// receive push events over a websocket, and filter them for the
/// event handler.
///
/// The default events that are queried are:
/// - [`EventType::NewBlock`](tendermint_rpc::query::EventType::NewBlock)
/// - [`EventType::Tx`](tendermint_rpc::query::EventType::Tx)
pub struct NearEventMonitor {
    ///
    chain_id: ChainId,
    /// near ibc address
    near_ibc_address: AccountId,
    /// The NEAR rpc client to collect IBC events
    client: NearRpcClient,
    /// Channel where to send EventBatch
    event_tx: Option<crossbeam_channel::Sender<Arc<Result<EventBatch>>>>,
    /// Channel where to receive commands
    rx_cmd: channel::Receiver<MonitorCmd>,
    /// Tokio runtime
    rt: Arc<TokioRuntime>,
    /// The heights that have already been checked for IBC events.
    checked_heights: Vec<u64>,
}

impl NearIbcContract for NearEventMonitor {
    type Error = NearError;

    fn get_contract_id(&self) -> AccountId {
        self.near_ibc_address.clone()
    }

    fn get_client(&self) -> &NearRpcClient {
        &self.client
    }

    fn get_rt(&self) -> &Arc<TokioRuntime> {
        &self.rt
    }
}

impl NearEventMonitor {
    /// Create an event monitor, and connect to a node
    #[instrument(
        name = "near_event_monitor.create",
        level = "error",
        skip_all,
        fields(chain = %chain_id, rpc_client = %rpc_addr)
    )]
    pub fn new(
        chain_id: ChainId,
        near_ibc_address: AccountId,
        rpc_addr: String,
        rt: Arc<TokioRuntime>,
    ) -> Result<(Self, TxMonitorCmd)> {
        let (tx_cmd, rx_cmd) = channel::unbounded();

        let client = NearRpcClient::new(rpc_addr.as_str());

        let monitor = Self {
            rt,
            near_ibc_address,
            chain_id,
            client,
            event_tx: None,
            rx_cmd,
            checked_heights: vec![],
        };

        Ok((monitor, TxMonitorCmd(tx_cmd)))
    }

    /// Event monitor loop
    #[allow(clippy::while_let_loop)]
    #[instrument(
        name = "event_monitor",
        level = "error",
        skip_all,
        fields(chain = %self.chain_id)
    )]
    pub fn run(mut self) {
        info!("Starting event monitor for {}", self.chain_id);

        // Continuously run the event loop, so that when it aborts
        // because of WebSocket client restart, we pick up the work again.
        loop {
            match self.run_loop() {
                Next::Continue => continue,
                Next::Abort => break,
            }
        }

        info!(
            "Event monitor for {} has successfully shut down.",
            self.chain_id
        );
    }

    fn run_loop(&mut self) -> Next {
        loop {
            if let Ok(cmd) = self.rx_cmd.try_recv() {
                match cmd {
                    MonitorCmd::Shutdown => return Next::Abort,
                    MonitorCmd::Subscribe(tx) => {
                        let (event_tx, event_rx) = crossbeam_channel::unbounded();
                        self.event_tx = Some(event_tx);
                        if let Err(e) = tx.send(event_rx) {
                            error!("failed to send back subscription: {e}");
                        }
                    }
                }
            }
            if self.event_tx.is_some() {
                let heights = self.get_ibc_events_heights();
                let unchecked_heights = heights
                    .iter()
                    .map(|h| h.revision_height())
                    .filter(|h| !self.checked_heights.contains(h))
                    .collect::<Vec<u64>>();
                if !unchecked_heights.is_empty() {
                    let height = unchecked_heights[0];
                    warn!("querying ibc events at height: {:?}", unchecked_heights);
                    let event_tx = self.event_tx.as_ref().unwrap();
                    match self.query_events_at_height(&Height::new(0, height).unwrap()) {
                        Ok(batch) => {
                            if !batch.events.is_empty() {
                                let filtered_events: Vec<IbcEventWithHeight> = batch
                                    .clone()
                                    .events
                                    .into_iter()
                                    .filter(|e| {
                                        matches!(
                                            e.event,
                                            IbcEvent::CloseInitChannel(_)
                                                | IbcEvent::TimeoutPacket(_)
                                                | IbcEvent::SendPacket(_)
                                                | IbcEvent::AcknowledgePacket(_)
                                        )
                                    })
                                    .collect();
                                warn!("ibc events found at height {}: {:?}", height, batch);
                                let mut batch = batch.clone();
                                batch.events = filtered_events;
                                if let Err(e) = event_tx.send(Arc::new(Ok(batch))) {
                                    error!("failed to send event batch: {}", e);
                                }
                            }
                        }
                        Err(e) => {
                            if let Err(e) = event_tx.send(Arc::new(Err(e))) {
                                error!("failed to send error in fetching event batch: {}", e);
                            }
                        }
                    }
                    self.checked_heights.push(height);
                }
            }
        }
    }

    fn get_ibc_events_heights(&self) -> Vec<Height> {
        self.get_rt()
            .block_on(self.get_client().view(
                self.get_contract_id(),
                "get_ibc_events_heights".to_string(),
                json!({}).to_string().into_bytes(),
            ))
            .map_or_else(
                |_| vec![],
                |result| result.json().expect("get ibc events height failed"),
            )
    }

    fn query_events_at_height(&self, height: &Height) -> Result<EventBatch> {
        self.get_rt()
            .block_on(self.get_client().view(
                self.get_contract_id(),
                "get_ibc_events_at".to_string(),
                json!({ "height": height }).to_string().into_bytes(),
            ))
            .map_or_else(
                |_| {
                    Ok(EventBatch {
                        height: *height,
                        events: vec![],
                        chain_id: self.chain_id.clone(),
                        tracking_id: TrackingId::new_uuid(),
                    })
                },
                |result| {
                    let ibc_events: Vec<ibc::core::events::IbcEvent> =
                        result.json().expect("near event to json failed");
                    Ok(EventBatch {
                        height: *height,
                        events: ibc_events
                            .iter()
                            .map(|event| IbcEventWithHeight {
                                height: *height,
                                event: convert_ibc_event_to_hermes_ibc_event(event)
                                    .expect("failed to convert ibc event"),
                            })
                            .collect(),
                        chain_id: self.chain_id.clone(),
                        tracking_id: TrackingId::new_uuid(),
                    })
                },
            )
    }
}
