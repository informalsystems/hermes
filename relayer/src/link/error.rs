use thiserror::Error;

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};

use crate::channel::ChannelError;
use crate::connection::ConnectionError;
use crate::error::Error;
use crate::foreign_client::ForeignClientError;
use crate::transfer::PacketError;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("failed with underlying error: {0}")]
    Failed(String),

    #[error("failed to establish link: channel/port '{0}'/'{1}' on chain {2} not in open or close state when packets and timeouts can be relayed")]
    ConstructorFailed(ChannelId, PortId, ChainId),

    #[error("failed with underlying error: {0}")]
    Generic(#[from] Error),

    #[error("link initialization failed during channel counterparty verification: {0}")]
    Initialization(ChannelError),

    #[error("failed to construct packet proofs for chain {0} with error: {1}")]
    PacketProofsConstructor(ChainId, Error),

    #[error("failed during query to chain id {0} with underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error("connection error: {0}:")]
    ConnectionError(#[from] ConnectionError),

    #[error("channel error:  {0}:")]
    ChannelError(#[from] ChannelError),

    #[error("failed during a client operation: {0}:")]
    ClientError(ForeignClientError),

    #[error("packet error: {0}:")]
    PacketError(#[from] PacketError),

    #[error("clearing of old packets failed")]
    OldPacketClearingFailed,

    #[error("chain error when sending messages: {0}")]
    SendError(Box<IbcEvent>),
}
