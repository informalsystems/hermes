pub mod encoder;
mod path_identifier;
pub mod server;
pub mod state;

use std::error::Error;
use std::net::{SocketAddr, ToSocketAddrs};
use std::sync::Arc;

use once_cell::sync::OnceCell;
use tokio::task::JoinHandle;
use tracing::{debug, warn};

pub use crate::state::TelemetryState;

pub fn new_state(
    tx_latency_submitted_min: u64,
    tx_latency_submitted_max: u64,
    tx_latency_confirmed_min: u64,
    tx_latency_confirmed_max: u64,
) -> Arc<TelemetryState> {
    Arc::new(TelemetryState::new(
        tx_latency_submitted_min,
        tx_latency_submitted_max,
        tx_latency_confirmed_min,
        tx_latency_confirmed_max,
    ))
}

static GLOBAL_STATE: OnceCell<Arc<TelemetryState>> = OnceCell::new();

pub fn init(
    tx_latency_submitted_min: u64,
    tx_latency_submitted_max: u64,
    tx_latency_confirmed_min: u64,
    tx_latency_confirmed_max: u64,
) -> &'static Arc<TelemetryState> {
    let new_state = new_state(
        tx_latency_submitted_min,
        tx_latency_submitted_max,
        tx_latency_confirmed_min,
        tx_latency_confirmed_max,
    );
    match GLOBAL_STATE.set(new_state) {
        Ok(_) => debug!("initialised telemetry global state"),
        Err(_) => debug!("telemetry global state was already set"),
    }
    GLOBAL_STATE.get().unwrap()
}

pub fn global() -> &'static Arc<TelemetryState> {
    match GLOBAL_STATE.get() {
        Some(state) => state,
        None => {
            warn!(
                "global telemetry state not set, will initialize it using default histogram ranges"
            );
            let new_state = new_state(500, 10000, 1000, 20000);
            match GLOBAL_STATE.set(new_state) {
                Ok(_) => debug!("initialised telemetry global state"),
                Err(_) => debug!("telemetry global state was already set"),
            }
            GLOBAL_STATE.get().unwrap()
        }
    }
}

pub type BoxError = Box<dyn Error + Send + Sync>;

pub fn spawn<A>(
    addr: A,
    state: Arc<TelemetryState>,
) -> Result<(SocketAddr, JoinHandle<Result<(), BoxError>>), BoxError>
where
    A: ToSocketAddrs + Send + 'static,
{
    let addr = addr.to_socket_addrs()?.next().unwrap();
    let handle = tokio::spawn(server::listen(addr, state));

    Ok((addr, handle))
}
