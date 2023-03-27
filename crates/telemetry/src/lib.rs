pub mod encoder;
mod path_identifier;
pub mod server;
pub mod state;

use std::error::Error;
use std::net::{SocketAddr, ToSocketAddrs};
use std::sync::Arc;

use once_cell::sync::Lazy;
use tokio::task::JoinHandle;

pub use crate::state::TelemetryState;

pub fn new_state() -> Arc<TelemetryState> {
    Arc::new(TelemetryState::default())
}

static GLOBAL_STATE: Lazy<Arc<TelemetryState>> = Lazy::new(new_state);

pub fn global() -> &'static Arc<TelemetryState> {
    &GLOBAL_STATE
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
