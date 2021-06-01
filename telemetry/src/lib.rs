pub mod server;
pub mod state;

use std::{sync::Arc, thread::JoinHandle};

pub use crate::state::TelemetryState;

pub fn new_state() -> Arc<TelemetryState> {
    Arc::new(TelemetryState::default())
}

pub fn spawn(port: u16, state: Arc<TelemetryState>) -> JoinHandle<()> {
    std::thread::spawn(move || server::run(state, port))
}
