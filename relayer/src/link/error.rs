use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;

use crate::channel::ChannelError;
use crate::connection::ConnectionError;
use crate::error::Error;
use crate::foreign_client::ForeignClientError;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("failed with underlying error: {0}")]
    Failed(String),

    #[error("failed to construct packet proofs for chain {0} with error: {1}")]
    PacketProofsConstructor(ChainId, Error),

    #[error("failed during query to chain id {0} with underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("Failed during a client operation: {0}:")]
    ClientError(ForeignClientError),

    #[error("PacketError:")]
    PacketError(#[from] Error),

    #[error("clearing of old packets failed")]
    OldPacketClearingFailed,
}
