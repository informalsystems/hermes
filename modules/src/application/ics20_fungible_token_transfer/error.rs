use crate::ics24_host::identifier::{ChannelId, PortId};
use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("unrecognized ICS-20 transfer message type URL {0}")]
    UnknownMessageTypeURL(String),

    #[error("the message is malformed and cannot be decoded")]
    MalformedMessageBytes,

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

    #[error("Module does not own a channel capability")]
    ChannelCapabilityNotFound,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
