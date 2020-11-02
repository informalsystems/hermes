use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("error raised by message handler")]
    HandlerRaisedError,

    #[error("error raised by the keeper functionality in message handler")]
    KeeperRaisedError,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
