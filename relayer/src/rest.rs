use crossbeam_channel::TryRecvError;
use serde::Serialize;
use tracing::{debug, error};

use crate::{
    config::{ChainConfig, Config},
    rest::request::{Request, VersionInfo},
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

pub enum Command {
    AddChain(ChainConfig),
}

/// Version response
#[derive(Serialize, Debug)]
pub struct Version {
    version: String,
}

impl Default for Version {
    fn default() -> Self {
        Self {
            version: option_env!("CARGO_PKG_VERSION")
                .unwrap_or("unknown")
                .to_string(),
        }
    }
}

/// Process incoming REST requests.
///
/// Non-blocking receiving of requests from
/// the REST server, and handles locally some of them.
/// Any request that cannot be handled is propagated
/// as a [`Command`], which the supervisor itself should handle.
pub fn process(config: &Config, channel: &Receiver) -> Option<Command> {
    match channel.try_recv() {
        Ok(request) => {
            match request {
                Request::Version { reply_to } => {
                    debug!("[rest/supervisor] Version");
                    let v = VersionInfo {
                        name: NAME.to_string(),
                        version: VER.to_string(),
                    };
                    reply_to.send(Ok(v)).unwrap();

                    // TODO(Adi): remove unwraps
                }

                Request::GetChains { reply_to } => {
                    debug!("[rest/supervisor] GetChains");
                    reply_to
                        .send(Ok(config.chains.iter().map(|c| c.id.clone()).collect()))
                        .unwrap();
                }

                Request::GetChain { chain_id, reply_to } => {
                    debug!("[rest/supervisor] GetChain {}", chain_id);
                    let result = config
                        .find_chain(&chain_id)
                        .cloned()
                        .ok_or_else(|| RestApiError::chain_config_not_found(chain_id));
                    reply_to.send(result).unwrap();
                } // Request::AddChain {
                  //     chain_config,
                  //     reply_to,
                  // } => {
                  //     debug!("[rest/supervisor] AddChain {}", chain_config);
                  //     reply_to.send(Ok(chain_config.clone())).unwrap();
                  //     let cfg: ChainConfig = serde_json::from_str(chain_config.as_str()).unwrap();
                  //     // Propagate the request to the supervisor
                  //     return Some(Command::AddChain(cfg));
                  // }
            }
        }
        Err(e) => {
            if !matches!(e, TryRecvError::Empty) {
                error!("[rest] error while waiting for requests: {}", e);
            }
        }
    }

    None
}
