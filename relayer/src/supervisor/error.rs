use thiserror::Error;

use ibc::ics24_host::identifier::{ChainId, ChannelId, ConnectionId};

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Error {
    #[error("channel {0} on chain {1} is not open")]
    ChannelUninitialized(ChannelId, ChainId),

    #[error("connection {0} (underlying channel {1}) on chain {2} is not open")]
    ConnectionNotOpen(ConnectionId, ChannelId, ChainId),

    #[error("channel {0} on chain {1} has no connection hops specified")]
    MissingConnectionHops(ChannelId, ChainId),

    #[error("query failed with error: {0}")]
    QueryFailed(String),
}
