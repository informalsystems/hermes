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

    // Count the number of trans
    pub relay_chains_num: BoundCounter<'static, u64>,
}

impl TelemetryState {
    pub fn new() -> TelemetryState {
        let exporter = opentelemetry_prometheus::exporter().init();
        let meter = global::meter("hermes");
        let telemetry_state = TelemetryState {
            exporter,
            relay_chains_num: meter
                .u64_counter("relay_chains_num")
                .with_description("Number of chains the relay is connecting to")
                .init()
                .bind(HANDLER_ALL.as_ref()),
        };
        telemetry_state
    }
}