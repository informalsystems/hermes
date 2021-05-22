use opentelemetry::metrics::BoundCounter;
use opentelemetry_prometheus::PrometheusExporter;
use opentelemetry::global;
use opentelemetry::KeyValue;

lazy_static! {
    static ref HANDLER_ALL: [KeyValue; 1] = [KeyValue::new("hermes", "all")];
}

pub struct TelemetryState {
    pub exporter: PrometheusExporter,

    // Count the number of trans
    pub packets_relayed: BoundCounter<'static, u64>,
}

impl TelemetryState {
    pub fn new() -> TelemetryState {
        let exporter = opentelemetry_prometheus::exporter().init();
        let meter = global::meter("hermes");
        let telemetry_state = TelemetryState {
            exporter,
            packets_relayed: meter
                .u64_counter("hermes.tx_count")
                .with_description("Total number of transactions processed via the relayer.")
                .init()
                .bind(HANDLER_ALL.as_ref()),
        };
        telemetry_state
    }
}