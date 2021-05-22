use prometheus::{Encoder, TextEncoder};

use crate::telemetry::service::MetricUpdate;
use crossbeam_channel::Sender;
use tracing::info;
use crate::telemetry::state::TelemetryState;

pub struct TelemetryServer {
    pub state: TelemetryState,
}

impl TelemetryServer {
    fn new(state: TelemetryState) -> TelemetryServer {
        TelemetryServer { state }
    }
}

impl TelemetryServer {
    fn run(listen_port: u16) -> () {
        let telemetry_state = TelemetryState::new();
        rouille::start_server(format!("localhost:{}", listen_port), move |request| {
            router!(request,
                // The prometheus endpoint
                (GET) (/metrics) => {
                    telemetry_state.packets_relayed.add(1);
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

    pub fn spawn(port: u16) -> Sender<MetricUpdate> {

        let (tx, _rx) = crossbeam_channel::unbounded();
        //let (service, tx) = TelemetryService::new(app_state.clone());
        //let server = TelemetryServer::new(app_state.clone());
        std::thread::spawn(move || TelemetryServer::run( port));
        //std::thread::spawn(|| service.run());

        tx
    }
}