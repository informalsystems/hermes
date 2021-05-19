use crossbeam_channel as channel;
use serde::Serialize;
use tracing::{debug, error};

use ibc::ics24_host::identifier::ChainId;

use crate::error::Kind as IBCErrorKind;
use crate::rest::Msg::AddChain;
use crate::{
    config::{ChainConfig, Config},
    error::Error,
};

pub type ReplyTo<T> = channel::Sender<Result<T, Error>>;
pub type Reply<T> = channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Request {
    Version {
        reply_to: ReplyTo<Version>,
    },
    AddChain {
        chain_config: ChainConfig,
        reply_to: ReplyTo<ChainConfig>,
    },
    GetChain {
        chain_id: ChainId,
        reply_to: ReplyTo<ChainConfig>,
    },
    GetChains {
        reply_to: ReplyTo<Vec<ChainId>>,
    },
}

pub enum Msg {
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

/// Process incoming requests. This goes into a `loop{}`, namely into the Supervisor's loop.
pub fn process(config: &Config, rest_receiver: &channel::Receiver<Request>) -> Option<Msg> {
    match rest_receiver.try_recv() {
        Ok(request) => {
            match request {
                Request::Version { reply_to } => {
                    debug!("REST: Version");
                    reply_to.send(Ok(Version::default())).unwrap();
                }
                Request::AddChain {
                    chain_config,
                    reply_to,
                } => {
                    debug!("REST: AddChain {}", chain_config.id.as_str());
                    reply_to.send(Ok(chain_config.clone())).unwrap();
                    // Propagate the request to the supervisor
                    return Some(AddChain(chain_config));
                }
                Request::GetChain { chain_id, reply_to } => {
                    debug!("REST: GetChain {}", chain_id.as_str());
                    let result = config
                        .find_chain(&chain_id)
                        .cloned()
                        .ok_or_else(|| IBCErrorKind::ChainIdNotFound(chain_id.to_string()).into());
                    reply_to.send(result).unwrap();
                }
                Request::GetChains { reply_to } => {
                    debug!("REST: GetChains");
                    reply_to
                        .send(Ok(config.chains.iter().map(|c| c.id.clone()).collect()))
                        .unwrap();
                }
            }
        }
        Err(e) => error!("error while waiting for requests: {}", e),
    }
    None
}
