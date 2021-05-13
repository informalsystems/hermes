use opentelemetry::metrics::BoundCounter;
use opentelemetry_prometheus::PrometheusExporter;

pub struct RelayerState {
    pub exporter: PrometheusExporter,
    pub tx_counter: BoundCounter<'static, u64>,
}
