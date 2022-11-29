extern crate alloc;

pub mod encoder;
mod path_identifier;
pub mod server;
pub mod state;

use alloc::sync::Arc;
use once_cell::sync::Lazy;
use std::{
    error::Error,
    net::{SocketAddr, ToSocketAddrs},
    thread::JoinHandle,
};

pub use crate::state::TelemetryState;

pub fn new_state() -> Arc<TelemetryState> {
    Arc::new(TelemetryState::default())
}

static GLOBAL_STATE: Lazy<Arc<TelemetryState>> = Lazy::new(new_state);

pub fn global() -> &'static Arc<TelemetryState> {
    &GLOBAL_STATE
}

pub fn spawn<A>(
    address: A,
    state: Arc<TelemetryState>,
) -> Result<(SocketAddr, JoinHandle<()>), Box<dyn Error + Send + Sync>>
where
    A: ToSocketAddrs + Send + 'static,
{
    let server = server::listen(address, state);

    match server {
        Ok(server) => {
            let address = server.server_addr();
            let handle = std::thread::spawn(move || server.run());

            Ok((address, handle))
        }
        Err(e) => Err(e),
    }
}
