use serde::Serialize;

use ibc::core::ics24_host::identifier::ChainId;

use crate::{config::ChainConfig, rest::RestApiError, supervisor::dump_state::SupervisorState};

pub type ReplySender<T> = crossbeam_channel::Sender<Result<T, RestApiError>>;
pub type ReplyReceiver<T> = crossbeam_channel::Receiver<Result<T, RestApiError>>;

pub fn reply_channel<T>() -> (ReplySender<T>, ReplyReceiver<T>) {
    crossbeam_channel::bounded(1)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VersionInfo {
    pub name: String,
    pub version: String,
}

/// REST API request variants
#[derive(Clone, Debug)]
pub enum Request {
    Version {
        reply_to: ReplySender<VersionInfo>,
    },

    State {
        reply_to: ReplySender<SupervisorState>,
    },

    GetChains {
        reply_to: ReplySender<Vec<ChainId>>,
    },

    GetChain {
        chain_id: ChainId,
        reply_to: ReplySender<ChainConfig>,
    },
}
