use crossbeam_channel::TryRecvError;
use tracing::{error, trace};

use crate::{
    config::Config,
    rest::request::ReplySender,
    rest::request::{Request, VersionInfo},
    supervisor::dump_state::SupervisorState,
};

pub mod request;

mod error;
pub use error::RestApiError;

pub const NAME: &str = env!(
    "CARGO_PKG_NAME",
    "the env. variable CARGO_PKG_NAME in ibc-relayer is not set!"
);
pub const VER: &str = env!(
    "CARGO_PKG_VERSION",
    "the env. variable CARGO_PKG_VERSION in ibc-relayer is not set!"
);

pub type Receiver = crossbeam_channel::Receiver<Request>;

// TODO: Unify this enum with `SupervisorCmd`
//  We won't unify yet as it is possible we will never implement
//  REST API `/chain` adding endpoint; instead of `/chain` we might
//  implement `/reload` for supporting a broader range of functionality
//  e.g., adjusting chain config, removing chains, etc.
pub enum Command {
    DumpState(ReplySender<SupervisorState>),
}

/// Process incoming REST requests.
///
/// Non-blocking receiving of requests from
/// the REST server, and tries to handle them locally.
///
/// Any request that cannot be handled locally here is propagated
/// as a [`Command`] to the caller, which the supervisor itself should handle.
pub fn process_incoming_requests(config: &Config, channel: &Receiver) -> Option<Command> {
    match channel.try_recv() {
        Ok(request) => match request {
            Request::Version { reply_to } => {
                trace!("Version");

                let v = VersionInfo {
                    name: NAME.to_string(),
                    version: VER.to_string(),
                };

                reply_to
                    .send(Ok(v))
                    .unwrap_or_else(|e| error!("error replying to a REST request {}", e));
            }

            Request::GetChains { reply_to } => {
                trace!("GetChains");

                reply_to
                    .send(Ok(config.chains.iter().map(|c| c.id.clone()).collect()))
                    .unwrap_or_else(|e| error!("error replying to a REST request {}", e));
            }

            Request::GetChain { chain_id, reply_to } => {
                trace!("GetChain {}", chain_id);

                let result = config
                    .find_chain(&chain_id)
                    .cloned()
                    .ok_or(RestApiError::ChainConfigNotFound(chain_id));

                reply_to
                    .send(result)
                    .unwrap_or_else(|e| error!("error replying to a REST request {}", e));
            }

            Request::State { reply_to } => {
                trace!("State");

                return Some(Command::DumpState(reply_to));
            }
        },
        Err(e) => {
            if !matches!(e, TryRecvError::Empty) {
                error!("error while waiting for requests: {}", e);
            }
        }
    }

    None
}
