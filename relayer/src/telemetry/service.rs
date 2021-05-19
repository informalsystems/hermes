use prometheus::{Encoder, TextEncoder};

use crate::telemetry::state::TelemetryState;
use std::sync::Arc;

pub struct TelemetryService {}

impl TelemetryService {
    pub fn run(state: Arc<TelemetryState>, listen_port: u16) -> () {
        rouille::start_server(format!("localhost:{}", listen_port), move |request| {
            router!(request,
                // The prometheus endpoint
                (GET) (/metrics) => {

                    state.tx_counter.add(1);

                    let mut buffer = vec![];
                    let encoder = TextEncoder::new();
                    let metric_families = state.exporter.registry().gather();
                    encoder.encode(&metric_families, &mut buffer).unwrap();

                    rouille::Response::from_data(encoder.format_type().to_string(), buffer)
                },

                // Any route other than /metrics
                // return an empty response with a 404 status code.
                _ => {
                    rouille::Response::empty_404()
                }
            )
        });
    }
}
