use core::fmt::{Display, Error as FmtError, Formatter};
use std::time::{Duration, Instant};

use dashmap::DashMap;
use opentelemetry::{
    global,
    metrics::{Counter, ObservableGauge, UpDownCounter},
    Context, KeyValue,
};
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::proto::MetricFamily;

use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};

use tendermint::Time;

use crate::path_identifier::PathIdentifier;

const EMPTY_BACKLOG_SYMBOL: u64 = 0;
const BACKLOG_CAPACITY: usize = 1000;
const BACKLOG_RESET_THRESHOLD: usize = 900;

const QUERY_TYPES_CACHE: [&str; 4] = [
    "query_latest_height",
    "query_client_state",
    "query_connection",
    "query_channel",
];

const QUERY_TYPES: [&str; 26] = [
    "query_latest_height",
    "query_block",
    "query_blocks",
    "query_packet_events",
    "query_txs",
    "query_next_sequence_receive",
    "query_unreceived_acknowledgements",
    "query_packet_acknowledgements",
    "query_unreceived_packets",
    "query_packet_commitments",
    "query_channel_client_state",
    "query_channel",
    "query_channels",
    "query_connection_channels",
    "query_connection",
    "query_connections",
    "query_client_connections",
    "query_consensus_state",
    "query_consensus_states",
    "query_upgraded_consensus_state",
    "query_client_state",
    "query_clients",
    "query_application_status",
    "query_commitment_prefix",
    "query_latest_height",
    "query_staking_params",
];

#[derive(Copy, Clone, Debug)]
pub enum WorkerType {
    Client,
    Connection,
    Channel,
    Packet,
    Wallet,
    CrossChainQuery,
}

impl Display for WorkerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            Self::Client => write!(f, "client"),
            Self::Connection => write!(f, "connection"),
            Self::Channel => write!(f, "channel"),
            Self::Packet => write!(f, "packet"),
            Self::Wallet => write!(f, "wallet"),
            Self::CrossChainQuery => write!(f, "cross-chain-query"),
        }
    }
}

pub struct TelemetryState {
    exporter: PrometheusExporter,

    /// Number of workers per type
    workers: UpDownCounter<i64>,

    /// Number of client update messages submitted per client
    client_updates_submitted: Counter<u64>,

    /// Number of misbehaviours detected and submitted per client
    client_misbehaviours_submitted: Counter<u64>,

    /// Number of confirmed receive packets per channel
    receive_packets_confirmed: Counter<u64>,

    /// Number of confirmed acknowledgment packets per channel
    acknowledgment_packets_confirmed: Counter<u64>,

    /// Number of confirmed timeout packets per channel
    timeout_packets_confirmed: Counter<u64>,

    /// Number of queries submitted by Hermes, per chain and query type
    queries: Counter<u64>,

    /// Number of cache hits for queries submitted by Hermes, per chain and query type
    queries_cache_hits: Counter<u64>,

    /// Number of times Hermes reconnected to the websocket endpoint, per chain
    ws_reconnect: Counter<u64>,

    /// How many IBC events did Hermes receive via the WebSocket subscription, per chain
    ws_events: Counter<u64>,

    /// Number of messages submitted to a specific chain
    total_messages_submitted: Counter<u64>,

    /// The balance of each wallet Hermes uses per chain
    wallet_balance: ObservableGauge<f64>,

    /// Indicates the latency for all transactions submitted to a specific chain,
    /// i.e. the difference between the moment when Hermes received a batch of events
    /// until the corresponding transaction(s) were submitted. Milliseconds.
    tx_latency_submitted: ObservableGauge<u64>,

    /// Indicates the latency for all transactions submitted to a specific chain,
    /// i.e. the difference between the moment when Hermes received a batch of events
    /// until the corresponding transaction(s) were confirmed. Milliseconds.
    tx_latency_confirmed: ObservableGauge<u64>,

    /// Records the time at which we started processing an event batch.
    /// Used for computing the `tx_latency` metric.
    in_flight_events: moka::sync::Cache<String, Instant>,

    /// Number of SendPacket events received
    send_packet_events: Counter<u64>,

    /// Number of WriteAcknowledgement events received
    acknowledgement_events: Counter<u64>,

    /// Number of Timeout events received
    timeout_events: Counter<u64>,

    /// Number of SendPacket events received during the initial and periodic clearing
    cleared_send_packet_events: Counter<u64>,

    /// Number of WriteAcknowledgement events received during the initial and periodic clearing
    cleared_acknowledgment_events: Counter<u64>,

    /// Records the sequence number of the oldest pending packet. This corresponds to
    /// the sequence number of the oldest SendPacket event for which no
    /// WriteAcknowledgement or Timeout events have been received. The value is 0 if all the
    /// SendPacket events were relayed.
    backlog_oldest_sequence: ObservableGauge<u64>,

    /// Record the timestamp related to `backlog_oldest_sequence`.
    /// The timestamp is the time passed since since the unix epoch in seconds.
    backlog_oldest_timestamp: ObservableGauge<u64>,

    /// Records the length of the backlog, i.e., how many packets are pending.
    backlog_size: ObservableGauge<u64>,

    /// Stores the backlogs for all the paths the relayer is active on.
    /// This is a map of multiple inner backlogs, one inner backlog per path.
    ///
    /// Each inner backlog is represented as a [`DashMap`].
    /// Each inner backlog captures the sequence numbers & timestamp for all SendPacket events
    /// that the relayer observed, and for which there was no associated Acknowledgement or
    /// Timeout event.
    backlogs: DashMap<PathIdentifier, DashMap<u64, u64>>,
}

impl TelemetryState {
    /// Gather the metrics for export
    pub fn gather(&self) -> Vec<MetricFamily> {
        self.exporter.registry().gather()
    }

    pub fn init_worker_by_type(&self, worker_type: WorkerType) {
        self.worker(worker_type, 0);
    }

    pub fn init_per_chain(&self, chain_id: &ChainId) {
        let cx = Context::current();

        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.ws_reconnect.add(&cx, 0, labels);
        self.ws_events.add(&cx, 0, labels);
        self.total_messages_submitted.add(&cx, 0, labels);

        self.init_queries(chain_id);
    }

    pub fn init_per_channel(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("src_channel", src_channel.to_string()),
            KeyValue::new("src_port", src_port.to_string()),
        ];

        self.receive_packets_confirmed.add(&cx, 0, labels);
        self.acknowledgment_packets_confirmed.add(&cx, 0, labels);
        self.timeout_packets_confirmed.add(&cx, 0, labels);
    }

    pub fn init_per_path(
        &self,
        chain: &ChainId,
        counterparty: &ChainId,
        channel: &ChannelId,
        port: &PortId,
        clear_packets: bool,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain.to_string()),
            KeyValue::new("counterparty", counterparty.to_string()),
            KeyValue::new("channel", channel.to_string()),
            KeyValue::new("port", port.to_string()),
        ];

        self.send_packet_events.add(&cx, 0, labels);
        self.acknowledgement_events.add(&cx, 0, labels);
        self.timeout_events.add(&cx, 0, labels);

        if clear_packets {
            self.cleared_send_packet_events.add(&cx, 0, labels);
            self.cleared_acknowledgment_events.add(&cx, 0, labels);
        }

        self.backlog_oldest_sequence.observe(&cx, 0, labels);
        self.backlog_oldest_timestamp.observe(&cx, 0, labels);
        self.backlog_size.observe(&cx, 0, labels);
    }

    pub fn init_per_client(
        &self,
        src_chain: &ChainId,
        dst_chain: &ChainId,
        client: &ClientId,
        misbehaviour: bool,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("dst_chain", dst_chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.client_updates_submitted.add(&cx, 0, labels);

        if misbehaviour {
            self.client_misbehaviours_submitted.add(&cx, 0, labels);
        }
    }

    fn init_queries(&self, chain_id: &ChainId) {
        let cx = Context::current();

        for query_type in QUERY_TYPES {
            let labels = &[
                KeyValue::new("chain", chain_id.to_string()),
                KeyValue::new("query_type", query_type),
            ];

            self.queries.add(&cx, 0, labels);
        }

        for query_type in QUERY_TYPES_CACHE {
            let labels = &[
                KeyValue::new("chain", chain_id.to_string()),
                KeyValue::new("query_type", query_type),
            ];

            self.queries_cache_hits.add(&cx, 0, labels);
        }
    }

    /// Update the number of workers per object
    pub fn worker(&self, worker_type: WorkerType, count: i64) {
        let cx = Context::current();
        let labels = &[KeyValue::new("type", worker_type.to_string())];
        self.workers.add(&cx, count, labels);
    }

    /// Update the number of client updates per client
    pub fn client_updates_submitted(
        &self,
        src_chain: &ChainId,
        dst_chain: &ChainId,
        client: &ClientId,
        count: u64,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("dst_chain", dst_chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.client_updates_submitted.add(&cx, count, labels);
    }

    /// Number of client misbehaviours per client
    pub fn client_misbehaviours_submitted(
        &self,
        src_chain: &ChainId,
        dst_chain: &ChainId,
        client: &ClientId,
        count: u64,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("dst_chain", dst_chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.client_misbehaviours_submitted.add(&cx, count, labels);
    }

    /// Number of receive packets relayed, per channel
    pub fn receive_packets_confirmed(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let cx = Context::current();

        if count > 0 {
            let labels = &[
                KeyValue::new("src_chain", src_chain.to_string()),
                KeyValue::new("src_channel", src_channel.to_string()),
                KeyValue::new("src_port", src_port.to_string()),
            ];

            self.receive_packets_confirmed.add(&cx, count, labels);
        }
    }

    /// Number of acknowledgment packets relayed, per channel
    pub fn acknowledgment_packets_confirmed(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let cx = Context::current();

        if count > 0 {
            let labels = &[
                KeyValue::new("src_chain", src_chain.to_string()),
                KeyValue::new("src_channel", src_channel.to_string()),
                KeyValue::new("src_port", src_port.to_string()),
            ];

            self.acknowledgment_packets_confirmed
                .add(&cx, count, labels);
        }
    }

    /// Number of timeout packets relayed, per channel
    pub fn timeout_packets_confirmed(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let cx = Context::current();

        if count > 0 {
            let labels = &[
                KeyValue::new("src_chain", src_chain.to_string()),
                KeyValue::new("src_channel", src_channel.to_string()),
                KeyValue::new("src_port", src_port.to_string()),
            ];

            self.timeout_packets_confirmed.add(&cx, count, labels);
        }
    }

    /// Number of queries emitted by the relayer, per chain and query type
    pub fn query(&self, chain_id: &ChainId, query_type: &'static str) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("query_type", query_type),
        ];

        self.queries.add(&cx, 1, labels);
    }

    /// Number of cache hits for queries emitted by the relayer, per chain and query type
    pub fn queries_cache_hits(&self, chain_id: &ChainId, query_type: &'static str) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("query_type", query_type),
        ];

        self.queries_cache_hits.add(&cx, 1, labels);
    }

    /// Number of time the relayer had to reconnect to the WebSocket endpoint, per chain
    pub fn ws_reconnect(&self, chain_id: &ChainId) {
        let cx = Context::current();

        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.ws_reconnect.add(&cx, 1, labels);
    }

    /// How many IBC events did Hermes receive via the WebSocket subscription, per chain
    pub fn ws_events(&self, chain_id: &ChainId, count: u64) {
        let cx = Context::current();

        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.ws_events.add(&cx, count, labels);
    }

    /// How many messages Hermes submitted to the chain
    pub fn total_messages_submitted(&self, chain_id: &ChainId, count: u64) {
        let cx = Context::current();

        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.total_messages_submitted.add(&cx, count, labels);
    }

    /// The balance in each wallet that Hermes is using, per account, denom and chain.
    /// The amount given is of unit: 10^6 * `denom`
    pub fn wallet_balance(&self, chain_id: &ChainId, account: &str, amount: f64, denom: &str) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("account", account.to_string()),
            KeyValue::new("denom", denom.to_string()),
        ];

        self.wallet_balance.observe(&cx, amount, labels);
    }

    pub fn received_event_batch(&self, tracking_id: impl ToString) {
        self.in_flight_events
            .insert(tracking_id.to_string(), Instant::now());
    }

    pub fn tx_submitted(
        &self,
        tx_count: usize,
        tracking_id: impl ToString,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let tracking_id = tracking_id.to_string();

        if let Some(start) = self.in_flight_events.get(&tracking_id) {
            let latency = start.elapsed().as_millis() as u64;

            let labels = &[
                // KeyValue::new("tracking_id", tracking_id),
                KeyValue::new("chain", chain_id.to_string()),
                KeyValue::new("counterparty", counterparty_chain_id.to_string()),
                KeyValue::new("channel", channel_id.to_string()),
                KeyValue::new("port", port_id.to_string()),
            ];

            for _ in 0..tx_count {
                self.tx_latency_submitted.observe(&cx, latency, labels);
            }
        }
    }

    pub fn tx_confirmed(
        &self,
        tx_count: usize,
        tracking_id: impl ToString,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let tracking_id = tracking_id.to_string();

        if let Some(start) = self.in_flight_events.get(&tracking_id) {
            let latency = start.elapsed().as_millis() as u64;

            let labels = &[
                // KeyValue::new("tracking_id", tracking_id),
                KeyValue::new("chain", chain_id.to_string()),
                KeyValue::new("counterparty", counterparty_chain_id.to_string()),
                KeyValue::new("channel", channel_id.to_string()),
                KeyValue::new("port", port_id.to_string()),
            ];

            for _ in 0..tx_count {
                self.tx_latency_confirmed.observe(&cx, latency, labels);
            }
        }
    }

    pub fn send_packet_events(
        &self,
        _seq_nr: u64,
        _height: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        self.send_packet_events.add(&cx, 1, labels);
    }

    pub fn acknowledgement_events(
        &self,
        _seq_nr: u64,
        _height: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        self.acknowledgement_events.add(&cx, 1, labels);
    }

    pub fn timeout_events(
        &self,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        self.timeout_events.add(&cx, 1, labels);
    }

    pub fn cleared_send_packet_events(
        &self,
        _seq_nr: u64,
        _height: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let labels: &[KeyValue; 4] = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        self.cleared_send_packet_events.add(&cx, 1, labels);
    }

    pub fn cleared_acknowledgment_events(
        &self,
        _seq_nr: u64,
        _height: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        let labels: &[KeyValue; 4] = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        self.cleared_acknowledgment_events.add(&cx, 1, labels);
    }

    /// Inserts in the backlog a new event for the given sequence number.
    /// This happens when the relayer observed a new SendPacket event.
    pub fn backlog_insert(
        &self,
        seq_nr: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        // Unique identifier for a chain/channel/port.
        let path_uid: PathIdentifier = PathIdentifier::new(
            chain_id.to_string(),
            channel_id.to_string(),
            port_id.to_string(),
        );

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        // Retrieve local timestamp when this SendPacket event was recorded.
        let now = Time::now();
        let timestamp = match now.duration_since(Time::unix_epoch()) {
            Ok(ts) => ts.as_secs(),
            Err(_) => 0,
        };

        // Update the backlog with the incoming data and retrieve the oldest values
        let (oldest_sn, oldest_ts, total) = if let Some(path_backlog) = self.backlogs.get(&path_uid)
        {
            // Avoid having the inner backlog map growing more than a given threshold, by removing
            // the oldest sequence number entry.
            if path_backlog.len() > BACKLOG_RESET_THRESHOLD {
                if let Some(min) = path_backlog.iter().map(|v| *v.key()).min() {
                    path_backlog.remove(&min);
                }
            }
            path_backlog.insert(seq_nr, timestamp);

            // Return the oldest event information to be recorded in telemetry
            if let Some(min) = path_backlog.iter().map(|v| *v.key()).min() {
                if let Some(oldest) = path_backlog.get(&min) {
                    (min, *oldest.value(), path_backlog.len() as u64)
                } else {
                    // Timestamp was not found, this should not happen, record a 0 ts.
                    (min, 0, path_backlog.len() as u64)
                }
            } else {
                // We just inserted a new key/value, so this else branch is unlikely to activate,
                // but it can happen in case of concurrent updates to the backlog.
                (
                    EMPTY_BACKLOG_SYMBOL,
                    EMPTY_BACKLOG_SYMBOL,
                    EMPTY_BACKLOG_SYMBOL,
                )
            }
        } else {
            // If there is no inner backlog for this path, create a new map to store it.
            let new_path_backlog = DashMap::with_capacity(BACKLOG_CAPACITY);
            new_path_backlog.insert(seq_nr, timestamp);
            // Record it in the global backlog
            self.backlogs.insert(path_uid, new_path_backlog);

            // Return the current event information to be recorded in telemetry
            (seq_nr, timestamp, 1)
        };

        // Update metrics to reflect the new state of the backlog
        self.backlog_oldest_sequence.observe(&cx, oldest_sn, labels);
        self.backlog_oldest_timestamp
            .observe(&cx, oldest_ts, labels);
        self.backlog_size.observe(&cx, total, labels);
    }

    /// Evicts from the backlog the event for the given sequence number.
    /// Removing events happens when the relayer observed either an acknowledgment
    /// or a timeout for a packet sequence number, which means that the corresponding
    /// packet was relayed.
    pub fn backlog_remove(
        &self,
        seq_nr: u64,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
        let cx = Context::current();

        // Unique identifier for a chain/channel/port path.
        let path_uid: PathIdentifier = PathIdentifier::new(
            chain_id.to_string(),
            channel_id.to_string(),
            port_id.to_string(),
        );

        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("counterparty", counterparty_chain_id.to_string()),
            KeyValue::new("channel", channel_id.to_string()),
            KeyValue::new("port", port_id.to_string()),
        ];

        if let Some(path_backlog) = self.backlogs.get(&path_uid) {
            if path_backlog.remove(&seq_nr).is_some() {
                // The oldest pending sequence number is the minimum key in the inner (path) backlog.
                if let Some(min_key) = path_backlog.iter().map(|v| *v.key()).min() {
                    if let Some(oldest) = path_backlog.get(&min_key) {
                        self.backlog_oldest_timestamp
                            .observe(&cx, *oldest.value(), labels);
                    } else {
                        self.backlog_oldest_timestamp.observe(&cx, 0, labels);
                    }
                    self.backlog_oldest_sequence.observe(&cx, min_key, labels);
                    self.backlog_size
                        .observe(&cx, path_backlog.len() as u64, labels);
                } else {
                    // No mimimum found, update the metrics to reflect an empty backlog
                    self.backlog_oldest_sequence
                        .observe(&cx, EMPTY_BACKLOG_SYMBOL, labels);
                    self.backlog_oldest_timestamp
                        .observe(&cx, EMPTY_BACKLOG_SYMBOL, labels);
                    self.backlog_size.observe(&cx, EMPTY_BACKLOG_SYMBOL, labels);
                }
            }
        }
    }
}

use std::sync::Arc;

use opentelemetry::metrics::Unit;
use opentelemetry::sdk::export::metrics::AggregatorSelector;
use opentelemetry::sdk::metrics::aggregators::Aggregator;
use opentelemetry::sdk::metrics::aggregators::{histogram, last_value, sum};
use opentelemetry::sdk::metrics::sdk_api::Descriptor;

#[derive(Debug)]
struct CustomAggregatorSelector;

impl AggregatorSelector for CustomAggregatorSelector {
    fn aggregator_for(&self, descriptor: &Descriptor) -> Option<Arc<dyn Aggregator + Send + Sync>> {
        match descriptor.name() {
            "wallet_balance" => Some(Arc::new(last_value())),
            "backlog_oldest_sequence" => Some(Arc::new(last_value())),
            "backlog_oldest_timestamp" => Some(Arc::new(last_value())),
            "backlog_size" => Some(Arc::new(last_value())),
            // Prometheus' supports only collector for histogram, sum, and last value aggregators.
            // https://docs.rs/opentelemetry-prometheus/0.11.0/src/opentelemetry_prometheus/lib.rs.html#411-418
            // TODO: Once quantile sketches are supported, replace histograms with that.
            "tx_latency_submitted" => Some(Arc::new(histogram(&[
                200.0, 500.0, 1000.0, 2000.0, 5000.0, 10000.0,
            ]))),
            "tx_latency_confirmed" => Some(Arc::new(histogram(&[
                1000.0, 5000.0, 9000.0, 13000.0, 17000.0, 20000.0,
            ]))),
            _ => Some(Arc::new(sum())),
        }
    }
}

impl Default for TelemetryState {
    fn default() -> Self {
        use opentelemetry::sdk::export::metrics::aggregation;
        use opentelemetry::sdk::metrics::{controllers, processors};

        let controller = controllers::basic(
            processors::factory(
                CustomAggregatorSelector,
                aggregation::cumulative_temporality_selector(),
            )
            .with_memory(true),
        )
        .build();

        let exporter = opentelemetry_prometheus::ExporterBuilder::new(controller).init();

        let meter = global::meter("hermes");

        Self {
            exporter,

            workers: meter
                .i64_up_down_counter("workers")
                .with_description("Number of workers")
                .init(),

            client_updates_submitted: meter
                .u64_counter("client_updates_submitted")
                .with_description("Number of client update messages submitted")
                .init(),

            client_misbehaviours_submitted: meter
                .u64_counter("client_misbehaviours_submitted")
                .with_description("Number of misbehaviours detected and submitted")
                .init(),

            receive_packets_confirmed: meter
                .u64_counter("receive_packets_confirmed")
                .with_description("Number of confirmed receive packets. Available if relayer runs with Tx confirmation enabled")
                .init(),

            acknowledgment_packets_confirmed: meter
                .u64_counter("acknowledgment_packets_confirmed")
                .with_description("Number of confirmed acknowledgment packets. Available if relayer runs with Tx confirmation enabled")
                .init(),

            timeout_packets_confirmed: meter
                .u64_counter("timeout_packets_confirmed")
                .with_description("Number of confirmed timeout packets. Available if relayer runs with Tx confirmation enabled")
                .init(),

            queries: meter
                .u64_counter("queries")
                .with_description(
                    "Number of queries submitted by Hermes",
                )
                .init(),

            queries_cache_hits: meter
                .u64_counter("queries_cache_hits")
                .with_description("Number of cache hits for queries submitted by Hermes")
                .init(),

            ws_reconnect: meter
                .u64_counter("ws_reconnect")
                .with_description("Number of times Hermes reconnected to the websocket endpoint")
                .init(),

            ws_events: meter
                .u64_counter("ws_events")
                .with_description("How many IBC events did Hermes receive via the websocket subscription")
                .init(),

            total_messages_submitted: meter
                .u64_counter("total_messages_submitted")
                .with_description("Number of messages submitted to a specific chain")
                .init(),

            wallet_balance: meter
                .f64_observable_gauge("wallet_balance")
                .with_description("The balance of each wallet Hermes uses per chain. Please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value")
                .init(),

            send_packet_events: meter
                .u64_counter("send_packet_events")
                .with_description("Number of SendPacket events received")
                .init(),

            acknowledgement_events: meter
                .u64_counter("acknowledgement_events")
                .with_description("Number of WriteAcknowledgement events received")
                .init(),

            timeout_events: meter
                .u64_counter("timeout_events")
                .with_description("Number of TimeoutPacket events received")
                .init(),

            cleared_send_packet_events: meter
                .u64_counter("cleared_send_packet_events")
                .with_description("Number of SendPacket events received during the initial and periodic clearing")
                .init(),

            cleared_acknowledgment_events: meter
                .u64_counter("cleared_acknowledgment_events")
                .with_description("Number of WriteAcknowledgement events received during the initial and periodic clearing")
                .init(),

            tx_latency_submitted: meter
                .u64_observable_gauge("tx_latency_submitted")
                .with_unit(Unit::new("milliseconds"))
                .with_description("The latency for all transactions submitted to a specific chain, \
                    i.e. the difference between the moment when Hermes received a batch of events \
                    and when it submitted the corresponding transaction(s). Milliseconds.")
                .init(),

            tx_latency_confirmed: meter
                .u64_observable_gauge("tx_latency_confirmed")
                .with_unit(Unit::new("milliseconds"))
                .with_description("The latency for all transactions submitted & confirmed to a specific chain, \
                    i.e. the difference between the moment when Hermes received a batch of events \
                    until the corresponding transaction(s) were confirmed. Milliseconds.")
                .init(),

            in_flight_events: moka::sync::Cache::builder()
                .time_to_live(Duration::from_secs(60 * 60)) // Remove entries after 1 hour
                .time_to_idle(Duration::from_secs(30 * 60)) // Remove entries if they have been idle for 30 minutes
                .build(),

            backlogs: DashMap::new(),

            backlog_oldest_sequence: meter
                .u64_observable_gauge("backlog_oldest_sequence")
                .with_description("Sequence number of the oldest SendPacket event in the backlog")
                .init(),

            backlog_oldest_timestamp: meter
                .u64_observable_gauge("backlog_oldest_timestamp")
                .with_unit(Unit::new("seconds"))
                .with_description("Local timestamp for the oldest SendPacket event in the backlog")
                .init(),

            backlog_size: meter
                .u64_observable_gauge("backlog_size")
                .with_description("Total number of SendPacket events in the backlog")
                .init(),
        }
    }
}
