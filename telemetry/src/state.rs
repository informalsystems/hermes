use core::fmt;
use std::time::{Duration, Instant};

use opentelemetry::{
    global,
    metrics::{Counter, UpDownCounter, ValueRecorder},
    KeyValue,
};
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::proto::MetricFamily;

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};

#[derive(Copy, Clone, Debug)]
pub enum WorkerType {
    Client,
    Connection,
    Channel,
    Packet,
    Wallet,
}

impl fmt::Display for WorkerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Client => write!(f, "client"),
            Self::Connection => write!(f, "connection"),
            Self::Channel => write!(f, "channel"),
            Self::Packet => write!(f, "packet"),
            Self::Wallet => write!(f, "wallet"),
        }
    }
}

pub struct TelemetryState {
    exporter: PrometheusExporter,

    /// Number of workers per object
    workers: UpDownCounter<i64>,

    /// Number of client updates per client
    ibc_client_updates: Counter<u64>,

    /// Number of client misbehaviours per client
    ibc_client_misbehaviours: Counter<u64>,

    /// Number of receive packets relayed, per channel
    receive_packets: Counter<u64>,

    /// Number of acknowledgment packets relayed, per channel
    acknowledgment_packets: Counter<u64>,

    /// Number of timeout packets relayed, per channel
    timeout_packets: Counter<u64>,

    /// Number of queries emitted by the relayer, per chain and query type
    queries: Counter<u64>,

    /// Number of cache hits for queries emitted by the relayer, per chain and query type
    query_cache_hits: Counter<u64>,

    /// Number of time the relayer had to reconnect to the WebSocket endpoint, per chain
    ws_reconnect: Counter<u64>,

    /// How many IBC events did Hermes receive via the WebSocket subscription, per chain
    ws_events: Counter<u64>,

    /// How many messages Hermes submitted to the chain, per chain
    msg_num: Counter<u64>,

    /// The balance in each wallet that Hermes is using, per wallet, denom and chain
    wallet_balance: ValueRecorder<u64>,

    /// Indicates the latency for all transactions submitted to a specific chain,
    /// i.e. the difference between the moment when Hermes received a batch of events
    /// until the corresponding transaction(s) were submitted. Milliseconds.
    tx_latency_submitted: ValueRecorder<u64>,

    /// Indicates the latency for all transactions submitted to a specific chain,
    /// i.e. the difference between the moment when Hermes received a batch of events
    /// until the corresponding transaction(s) were confirmed. Milliseconds.
    tx_latency_confirmed: ValueRecorder<u64>,

    /// Records the time at which we started processing an event batch.
    /// Used for computing the `tx_latency` metric.
    in_flight_events: moka::sync::Cache<String, Instant>,
}

impl TelemetryState {
    /// Gather the metrics for export
    pub fn gather(&self) -> Vec<MetricFamily> {
        self.exporter.registry().gather()
    }

    /// Update the number of workers per object
    pub fn worker(&self, worker_type: WorkerType, count: i64) {
        let labels = &[KeyValue::new("type", worker_type.to_string())];
        self.workers.add(count, labels);
    }

    /// Update the number of client updates per client
    pub fn ibc_client_updates(&self, chain: &ChainId, client: &ClientId, count: u64) {
        let labels = &[
            KeyValue::new("chain", chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.ibc_client_updates.add(count, labels);
    }

    /// Number of client misbehaviours per client
    pub fn ibc_client_misbehaviour(&self, chain: &ChainId, client: &ClientId, count: u64) {
        let labels = &[
            KeyValue::new("chain", chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.ibc_client_misbehaviours.add(count, labels);
    }

    /// Number of receive packets relayed, per channel
    pub fn ibc_receive_packets(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("src_channel", src_channel.to_string()),
            KeyValue::new("src_port", src_port.to_string()),
        ];

        self.receive_packets.add(count, labels);
    }

    /// Number of acknowledgment packets relayed, per channel
    pub fn ibc_acknowledgment_packets(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("src_channel", src_channel.to_string()),
            KeyValue::new("src_port", src_port.to_string()),
        ];

        self.acknowledgment_packets.add(count, labels);
    }

    /// Number of timeout packets relayed, per channel
    pub fn ibc_timeout_packets(
        &self,
        src_chain: &ChainId,
        src_channel: &ChannelId,
        src_port: &PortId,
        count: u64,
    ) {
        let labels = &[
            KeyValue::new("src_chain", src_chain.to_string()),
            KeyValue::new("src_channel", src_channel.to_string()),
            KeyValue::new("src_port", src_port.to_string()),
        ];

        self.timeout_packets.add(count, labels);
    }

    /// Number of queries emitted by the relayer, per chain and query type
    pub fn query(&self, chain_id: &ChainId, query_type: &'static str) {
        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("query_type", query_type),
        ];

        self.queries.add(1, labels);
    }

    /// Number of cache hits for queries emitted by the relayer, per chain and query type
    pub fn query_cache_hit(&self, chain_id: &ChainId, query_type: &'static str) {
        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("query_type", query_type),
        ];

        self.query_cache_hits.add(1, labels);
    }

    /// Number of time the relayer had to reconnect to the WebSocket endpoint, per chain
    pub fn ws_reconnect(&self, chain_id: &ChainId) {
        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.ws_reconnect.add(1, labels);
    }

    /// How many IBC events did Hermes receive via the WebSocket subscription, per chain
    pub fn ws_events(&self, chain_id: &ChainId, count: u64) {
        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.ws_events.add(count, labels);
    }

    /// How many messages Hermes submitted to the chain, per chain
    pub fn msg_num(&self, chain_id: &ChainId, count: u64) {
        let labels = &[KeyValue::new("chain", chain_id.to_string())];

        self.msg_num.add(count, labels);
    }

    /// The balance in each wallet that Hermes is using, per account, denom and chain
    pub fn wallet_balance(&self, chain_id: &ChainId, account: &str, amount: u64, denom: &str) {
        let labels = &[
            KeyValue::new("chain", chain_id.to_string()),
            KeyValue::new("account", account.to_string()),
            KeyValue::new("denom", denom.to_string()),
        ];

        self.wallet_balance.record(amount, labels);
    }

    pub fn received_event_batch(&self, tracking_id: impl ToString) {
        self.in_flight_events
            .insert(tracking_id.to_string(), Instant::now());
    }

    pub fn tx_submitted(
        &self,

        tracking_id: impl ToString,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
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

            self.tx_latency_submitted.record(latency, labels);
        }
    }

    pub fn tx_confirmed(
        &self,
        tracking_id: impl ToString,
        chain_id: &ChainId,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_chain_id: &ChainId,
    ) {
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

            self.tx_latency_confirmed.record(latency, labels);
        }
    }
}

use std::sync::Arc;

use opentelemetry::metrics::Descriptor;
use opentelemetry::sdk::export::metrics::{Aggregator, AggregatorSelector};
use opentelemetry::sdk::metrics::aggregators::{histogram, last_value, sum};

#[derive(Debug)]
struct CustomAggregatorSelector;
impl AggregatorSelector for CustomAggregatorSelector {
    fn aggregator_for(&self, descriptor: &Descriptor) -> Option<Arc<dyn Aggregator + Send + Sync>> {
        match descriptor.name() {
            "wallet_balance" => Some(Arc::new(last_value())),
            "tx_latency_submitted" => Some(Arc::new(histogram(descriptor, &[0.5, 0.9, 0.99]))),
            "tx_latency_confirmed" => Some(Arc::new(histogram(descriptor, &[0.5, 0.9, 0.99]))),
            _ => Some(Arc::new(sum())),
        }
    }
}

impl Default for TelemetryState {
    fn default() -> Self {
        let exporter = opentelemetry_prometheus::ExporterBuilder::default()
            .with_aggregator_selector(CustomAggregatorSelector)
            .init();

        let meter = global::meter("hermes");

        Self {
            exporter,

            workers: meter
                .i64_up_down_counter("workers")
                .with_description("Number of workers per object")
                .init(),

            ibc_client_updates: meter
                .u64_counter("ibc_client_updates")
                .with_description("Number of client updates performed per client")
                .init(),

            ibc_client_misbehaviours: meter
                .u64_counter("ibc_client_misbehaviours")
                .with_description("Number of misbehaviours detected per client")
                .init(),

            receive_packets: meter
                .u64_counter("ibc_receive_packets")
                .with_description("Number of receive packets relayed per channel")
                .init(),

            acknowledgment_packets: meter
                .u64_counter("ibc_acknowledgment_packets")
                .with_description("Number of acknowledgment packets relayed per channel")
                .init(),

            timeout_packets: meter
                .u64_counter("ibc_timeout_packets")
                .with_description("Number of timeout packets relayed per channel")
                .init(),

            queries: meter
                .u64_counter("queries")
                .with_description(
                    "Number of queries emitted by the relayer, per chain and query type",
                )
                .init(),

            query_cache_hits: meter
                .u64_counter("cache_hits")
                .with_description("Number of cache hits for queries emitted by the relayer, per chain and query type")
                .init(),

            ws_reconnect: meter
                .u64_counter("ws_reconnect")
                .with_description("Number of time the relayer had to reconnect to the WebSocket endpoint, per chain")
                .init(),

            ws_events: meter
                .u64_counter("ws_events")
                .with_description("How many IBC events did Hermes receive via the WebSocket subscription, per chain")
                .init(),

            msg_num: meter
                .u64_counter("msg_num")
                .with_description("How many messages Hermes submitted to the chain, per chain")
                .init(),

            wallet_balance: meter
                .u64_value_recorder("wallet_balance")
                .with_description("The balance in each wallet that Hermes is using, per wallet, denom and chain")
                .init(),

            tx_latency_submitted: meter
                .u64_value_recorder("tx_latency_submitted")
                .with_description("The latency for all transactions submitted to a specific chain, \
                    i.e. the difference between the moment when Hermes received a batch of events \
                    and when it submitted the corresponding transaction(s). Milliseconds.")
                .init(),

            tx_latency_confirmed: meter
                .u64_value_recorder("tx_latency_confirmed")
                .with_description("The latency for all transactions submitted to a specific chain, \
                    i.e. the difference between the moment when Hermes received a batch of events \
                    until the corresponding transaction(s) were confirmed. Milliseconds.")
                .init(),

            in_flight_events: moka::sync::Cache::builder()
                    .time_to_live(Duration::from_secs(60 * 60)) // Remove entries after 1 hour
                    .time_to_idle(Duration::from_secs(30 * 60)) // Remove entries if they have been idle for 30 minutes
                    .build(),
        }
    }
}
