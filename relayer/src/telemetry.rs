use crate::telemetry::state::TelemetryState;
use crate::telemetry::service::TelemetryService;
use crate::telemetry::server::TelemetryServer;
use crossbeam_channel::Sender;
use crate::telemetry::service::MetricUpdate;

pub mod service;
pub mod server;
pub mod state;

pub fn spawn(port: u16) -> Sender<MetricUpdate> {
    let (tx, rx) = crossbeam_channel::unbounded();
    let telemetry_state = TelemetryState::new();
    let service = TelemetryService::new(telemetry_state.clone(), rx);
    let server = TelemetryServer::new(telemetry_state.clone());

    // Start the telemetry service and server
    std::thread::spawn(move || server.run( telemetry_state.clone(),port));
    std::thread::spawn(move || service.run());

    tx
}