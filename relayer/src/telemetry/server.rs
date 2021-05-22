use prometheus::{Encoder, TextEncoder};
use tracing::info;
use crate::telemetry::state::TelemetryState;

pub struct TelemetryServer {
    pub state: TelemetryState,
}

impl TelemetryServer {
    pub(crate) fn new(state: TelemetryState) -> TelemetryServer {
        TelemetryServer { state }
    }

    pub(crate) fn run(&self, telemetry_state: TelemetryState, listen_port: u16) -> () {
        rouille::start_server(format!("localhost:{}", listen_port), move |request| {
            router!(request,
                // The prometheus endpoint
                (GET) (/metrics) => {
                    //telemetry_state.packets_relayed.add(1);
                    info!("metrics called on telemetry server");
                    let mut buffer = vec![];
                    let encoder = TextEncoder::new();
                    let metric_families = telemetry_state.exporter.registry().gather();
                    encoder.encode(&metric_families, &mut buffer).unwrap();
                    dbg!(metric_families);
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