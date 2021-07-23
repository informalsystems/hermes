use thiserror::Error;

use ibc::ics04_channel::channel::State;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortChannelId, PortId};

use crate::error::Error;
use crate::foreign_client::ForeignClientError;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("failed due to missing local channel id")]
    MissingLocalChannelId,

    #[error("failed due to missing counterparty channel id")]
    MissingCounterpartyChannelId,

    #[error("failed due to missing counterparty connection")]
    MissingCounterpartyConnection,

    #[error("channel constructor failed due to missing connection id on chain id {0}")]
    MissingLocalConnection(ChainId),

    #[error("failed during an operation on client ({0}) hosted by chain ({1}) with error: {2}")]
    ClientOperation(ClientId, ChainId, ForeignClientError),

    #[error("failed during a query to chain id {0} with underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    SubmitError(ChainId, Error),

    #[error("failed to finalize a channel open handshake while querying for channel end {0}/{1} on chain chain {2}: {3}")]
    HandshakeFinalize(PortId, ChannelId, ChainId, String),

    #[error("the channel is partially open ({0}, {1})")]
    PartialOpenHandshake(State, State),

    #[error("channel {0} on chain {1} has no counterparty channel id")]
    IncompleteChannelState(PortChannelId, ChainId),

    #[error("channel {0} on chain {1} expected to have counterparty {2} (but instead has {3})")]
    MismatchingChannelEnds(PortChannelId, ChainId, PortChannelId, PortChannelId),
}
