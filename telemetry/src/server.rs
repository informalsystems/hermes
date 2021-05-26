use std::sync::Arc;

use prometheus::{Encoder, TextEncoder};
use rouille::router;

use crate::state::TelemetryState;

#[allow(clippy::manual_strip)]
pub fn run(telemetry_state: Arc<TelemetryState>, port: u16) {
    rouille::start_server(("localhost", port), move |request| {
        router!(request,
            // The prometheus endpoint
            (GET) (/metrics) => {
                let mut buffer = vec![];
                let encoder = TextEncoder::new();
                let metric_families = telemetry_state.exporter.registry().gather();
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
