use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("unrecognized ICS-20 transfer message type URL {0}")]
    UnknownMessageTypeURL(String),

    #[error("the message is malformed and cannot be decoded")]
    MalformedMessageBytes,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
