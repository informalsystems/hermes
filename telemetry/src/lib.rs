pub mod server;

pub mod service;
pub use service::TelemetryService;

pub mod state;
pub use state::TelemetryState;

pub mod metric;
pub use metric::MetricUpdate;

use std::sync::Arc;

use crossbeam_channel::Sender;

#[derive(Clone, Debug)]
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

    let telemetry_state = Arc::new(TelemetryState::default());
    let service = TelemetryService::new(telemetry_state.clone(), rx);

    // Start the telemetry service and server
    std::thread::spawn(move || server::run(telemetry_state, port));
    std::thread::spawn(move || service.run());

    TelemetryHandle { tx: Some(tx) }
}
