use once_cell::sync::Lazy;
use opentelemetry::{global, metrics::BoundCounter, KeyValue};
use opentelemetry_prometheus::PrometheusExporter;

static HANDLER_ALL: Lazy<[KeyValue; 1]> = Lazy::new(|| [KeyValue::new("hermes", "all")]);

#[derive(Clone, Debug)]
pub struct TelemetryState {
    pub exporter: PrometheusExporter,

    // Number of chains the relay is connecting to
    pub relay_chains_num: BoundCounter<'static, u64>,

    // Number of channels the relay is connecting to
    pub relay_channels_num: BoundCounter<'static, u64>,

    // Total number of IBC packets acknowledged
    pub tx_msg_ibc_acknowledge_packet: BoundCounter<'static, u64>,

    // Total number of txs processed via relay tx
    pub tx_count: BoundCounter<'static, u64>,

    // Total number of successful txs processed via relay tx
    pub tx_successful: BoundCounter<'static, u64>,

    // Total number of failed txs processed via relay tx
    pub tx_failed: BoundCounter<'static, u64>,

    // Total number of IBC transfers sent from a chain (source or sink)
    pub ibc_transfer_send: BoundCounter<'static, u64>,

    // Total number of IBC transfers received to a chain (source or sink)
    pub ibc_transfer_receive: BoundCounter<'static, u64>,

    // Total number of IBC packets received
    pub tx_msg_ibc_recv_packet: BoundCounter<'static, u64>,

    // Total number of IBC timeout packets
    pub ibc_timeout_packet: BoundCounter<'static, u64>,

    // Total number of client misbehaviours
    pub ibc_client_misbehaviour: BoundCounter<'static, u64>,
}

impl Default for TelemetryState {
    fn default() -> Self {
        let exporter = opentelemetry_prometheus::exporter().init();
        let meter = global::meter("hermes");

        Self {
            exporter,
            relay_chains_num: meter
                .u64_counter("hermes_chains_num")
                .with_description("Number of chains the relay is connecting to")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            relay_channels_num: meter
                .u64_counter("hermes_channels_num")
                .with_description("Number of channels the relay is connecting to")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            tx_msg_ibc_acknowledge_packet: meter
                .u64_counter("hermes_tx_msg_ibc_acknowledge_packet")
                .with_description("Total number of IBC packets acknowledged")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            tx_count: meter
                .u64_counter("hermes_tx_count")
                .with_description("Total number of txs processed via relay tx")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            tx_successful: meter
                .u64_counter("hermes_tx_successful")
                .with_description("Total number of successful txs processed via relay tx")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            tx_failed: meter
                .u64_counter("hermes_tx_failed")
                .with_description("Total number of failed txs processed via relay tx")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            ibc_transfer_send: meter
                .u64_counter("hermes_ibc_transfer_send")
                .with_description(
                    "Total number of IBC transfers sent from a chain (source or sink)",
                )
                .init()
                .bind(HANDLER_ALL.as_ref()),
            ibc_transfer_receive: meter
                .u64_counter("hermes_ibc_transfer_receive")
                .with_description(
                    "Total number of IBC transfers received to a chain (source or sink)",
                )
                .init()
                .bind(HANDLER_ALL.as_ref()),
            tx_msg_ibc_recv_packet: meter
                .u64_counter("hermes_tx_msg_ibc_recv_packet")
                .with_description("Total number of IBC packets received")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            ibc_timeout_packet: meter
                .u64_counter("hermes_ibc_timeout_packet")
                .with_description("Total number of IBC timeout packets")
                .init()
                .bind(HANDLER_ALL.as_ref()),
            ibc_client_misbehaviour: meter
                .u64_counter("hermes_ibc_client_misbehaviour")
                .with_description("Total number of client misbehaviours")
                .init()
                .bind(HANDLER_ALL.as_ref()),
        }
    }
}
