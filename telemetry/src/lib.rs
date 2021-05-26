pub mod server;
pub mod service;
pub mod state;

use crossbeam_channel::Sender;

use crate::{
    server::TelemetryServer,
    service::{MetricUpdate, TelemetryService},
    state::TelemetryState,
};

pub struct TelemetryHandle {
    tx: Option<Sender<MetricUpdate>>,
}

impl TelemetryHandle {
    pub fn noop() -> Self {
        Self { tx: None }
    }

    pub fn send(&self, update: MetricUpdate) {
        if let Some(ref tx) = self.tx {
            let _ = tx.send(update);
        }
    }
}

pub fn spawn(port: u16, enabled: bool) -> TelemetryHandle {
    let (tx, rx) = crossbeam_channel::unbounded();

    // Only start the telemetry service and server if it is enabled in the configuration
    if !enabled {
        return TelemetryHandle::noop();
    }

    let telemetry_state = TelemetryState::default();

    let service = TelemetryService::new(telemetry_state.clone(), rx);
    let server = TelemetryServer::new(telemetry_state.clone());

    // Start the telemetry service and server
    std::thread::spawn(move || server.run(telemetry_state.clone(), port));
    std::thread::spawn(move || service.run());

    TelemetryHandle { tx: Some(tx) }
}
