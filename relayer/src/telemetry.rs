use crate::telemetry::server::TelemetryServer;
use crate::telemetry::service::MetricUpdate;
use crate::telemetry::service::TelemetryService;
use crate::telemetry::state::TelemetryState;
use crossbeam_channel::Sender;

pub mod server;
pub mod service;
pub mod state;

pub fn spawn(port: u16, enabled: bool) -> Sender<MetricUpdate> {
    let (tx, rx) = crossbeam_channel::unbounded();

    // Only start the telemetry service and server if it is enabled in the configuration
    if enabled {
        let telemetry_state = TelemetryState::new();
        let service = TelemetryService::new(telemetry_state.clone(), rx);
        let server = TelemetryServer::new(telemetry_state.clone());

        // Start the telemetry service and server
        std::thread::spawn(move || server.run(telemetry_state.clone(), port));
        std::thread::spawn(move || service.run());
    }

    tx
}
