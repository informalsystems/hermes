use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics24_host::identifier::{ChannelId, PortId};

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("unrecognized ICS-20 transfer message type URL {0}")]
    UnknownMessageTypeUrl(String),

    #[error("error raised by message handler")]
    HandlerRaisedError,

    #[error("Sending sequence number not found for port {0} and channel {1}")]
    SequenceSendNotFound(PortId, ChannelId),

    #[error("Missing channel for port_id {0} and channel_id {1} ")]
    ChannelNotFound(PortId, ChannelId),

    #[error(
        "Destination channel not found in the counterparty of port_id {0} and channel_id {1} "
    )]
    DestinationChannelNotFound(PortId, ChannelId),
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
