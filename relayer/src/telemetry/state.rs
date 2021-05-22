use opentelemetry::metrics::BoundCounter;
use opentelemetry_prometheus::PrometheusExporter;
use opentelemetry::global;
use opentelemetry::KeyValue;

lazy_static! {
    static ref HANDLER_ALL: [KeyValue; 1] = [KeyValue::new("hermes", "all")];
}

#[derive(Clone)]
pub struct TelemetryState {
    pub exporter: PrometheusExporter,

    // Number of chains the relay is connecting to
    pub relay_chains_num: BoundCounter<'static, u64>,

    // Number of channels the relay is connecting to
    pub relay_channels_num: BoundCounter<'static, u64>,

    // Total number of IBC packets acknowledged
    pub tx_msg_ibc_acknowledge_packet: BoundCounter<'static, u64>,

    // Total number of txs processed via Relay tx
    pub tx_count: BoundCounter<'static, u64>,

}

impl TelemetryState {
    pub fn new() -> TelemetryState {
        let exporter = opentelemetry_prometheus::exporter().init();
        let meter = global::meter("hermes");
        let telemetry_state = TelemetryState {
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
                .u64_counter("tx_count")
                .with_description("Total number of txs processed via Relay tx")
                .init()
                .bind(HANDLER_ALL.as_ref()),
        };
        telemetry_state
    }
}