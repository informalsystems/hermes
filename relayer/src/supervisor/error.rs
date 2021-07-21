use thiserror::Error;

use ibc::ics03_connection::connection::Counterparty;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId};

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Error {
    #[error("port/channel {0}/{1} on chain {1} is not initialized")]
    ChannelUninitialized(PortId, ChannelId, ChainId),

    #[error("channel {0} on chain {1} has a connection with uninitialized counterparty {:2}")]
    ChannelConnectionUninitialized(ChannelId, ChainId, Counterparty),

    #[error("connection {0} (underlying channel {1}) on chain {2} is not open")]
    ConnectionNotOpen(ConnectionId, ChannelId, ChainId),

    #[error("channel {0} on chain {1} has no connection hops specified")]
    MissingConnectionHops(ChannelId, ChainId),

    #[error("query failed with error: {0}")]
    QueryFailed(String),

    #[error("supervisor was not able to connect to any chains")]
    NoChainsAvailable,

    #[error("failed to spawn chain runtime: {0}")]
    FailedToSpawnChainRuntime(String),
}
