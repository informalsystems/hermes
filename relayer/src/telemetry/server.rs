use crate::telemetry::state::TelemetryState;
use prometheus::{Encoder, TextEncoder};

pub struct TelemetryServer {
    pub state: TelemetryState,
}

impl TelemetryServer {
    pub(crate) fn new(state: TelemetryState) -> TelemetryServer {
        TelemetryServer { state }
    }

    #[allow(clippy::manual_strip)]
    pub(crate) fn run(&self, telemetry_state: TelemetryState, listen_port: u16) {
        rouille::start_server(format!("localhost:{}", listen_port), move |request| {
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
}
