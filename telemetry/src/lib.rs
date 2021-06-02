pub mod server;
pub mod state;

use std::{net::ToSocketAddrs, sync::Arc, thread::JoinHandle};

pub use crate::state::TelemetryState;

pub fn new_state() -> Arc<TelemetryState> {
    Arc::new(TelemetryState::default())
}

pub fn spawn<A>(address: A, state: Arc<TelemetryState>) -> JoinHandle<()>
where
    A: ToSocketAddrs + Send + 'static,
{
    std::thread::spawn(move || server::run(address, state))
}
