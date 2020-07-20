use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    /// RPC error (typically raised by the RPC client or the RPC requester)
    #[error("RPC error")]
    Rpc,

    /// Event error (raised by the event monitor)
    #[error("Bad Notification")]
    Event,

    /// Response parsing error
    #[error("Could not parse/unmarshall response")]
    ResponseParsing,

    #[error("Empty response value")]
    EmptyResponseValue,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
