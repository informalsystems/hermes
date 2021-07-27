use serde::Serialize;

use ibc::ics24_host::error::ValidationKind;
use ibc::ics24_host::identifier::ChainId;

/// Various kinds of errors that can be raiser by the relayer.
#[derive(Clone, Debug, thiserror::Error, Serialize)]
pub enum Error {
    #[error("failed to send a request through crossbeam channel: {0}")]
    ChannelSend(String),

    #[error("failed to receive a reply from crossbeam channel: {0}")]
    ChannelRecv(String),

    #[error("failed while serializing reply into json value: {0}")]
    Serialization(String),

    #[error("could not find configuration for chain id {0}")]
    ChainConfigNotFound(ChainId),

    #[error("failed to parse the string {0} into a valid chain identifier: {1}")]
    InvalidChainId(String, ValidationKind),
}
