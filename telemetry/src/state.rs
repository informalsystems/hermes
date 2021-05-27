use opentelemetry::{
    global,
    metrics::{Counter, UpDownCounter},
    KeyValue,
};
use opentelemetry_prometheus::PrometheusExporter;

use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};

use crate::metric::{Op, WorkerType};

#[derive(Debug)]
pub struct TelemetryState {
    pub exporter: PrometheusExporter,

    /// Number of workers per object
    pub workers: UpDownCounter<i64>,

    /// Number of client misbehaviours per client
    pub ibc_client_misbehaviours: Counter<u64>,

    /// Number of receive packets relayed, per channel
    pub receive_packets: Counter<u64>,
}

impl TelemetryState {
    pub fn worker(&self, worker_type: WorkerType, op: Op) {
        let labels = &[KeyValue::new("type", worker_type.to_string())];
        self.workers.add(op.to_i64(), labels);
    }

    pub fn ibc_client_misbehaviour(&self, chain: &ChainId, client: &ClientId) {
        let labels = &[
            KeyValue::new("chain", chain.to_string()),
            KeyValue::new("client", client.to_string()),
        ];

        self.ibc_client_misbehaviours.add(1, labels);
    }

    pub fn receive_packets(
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
}

// Supervisor:
// - [x] number of workers per type (gauge)
//
// Client:
// - [x] misbehaviors per client (counter)
// - [ ] updates per client (counter) √
//
// Packet:
// - [ ] write acknowledgment events per object, wo/ destination (counter) √
// => `receive_packets`

impl Default for TelemetryState {
    fn default() -> Self {
        let exporter = opentelemetry_prometheus::exporter().init();
        let meter = global::meter("hermes");

        Self {
            exporter,

            workers: meter
                .i64_up_down_counter("workers")
                .with_description("Number of workers per object")
                .init(),

            ibc_client_misbehaviours: meter
                .u64_counter("ibc_client_misbehaviours")
                .with_description("Number of misbehaviours detected per client")
                .init(),

            receive_packets: meter
                .u64_counter("receive_packets")
                .with_description("Number of receive packets relayed per channel")
                .init(),
        }
    }
}
