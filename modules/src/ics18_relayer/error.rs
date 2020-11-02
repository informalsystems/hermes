use crate::ics24_host::identifier::ClientId;
use crate::Height;
use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("client state on destination chain not found, (client id: {0})")]
    ClientStateNotFound(ClientId),

    #[error("the client on destination chain is already up-to-date (client id: {0}, source height: {1}, dest height: {2})")]
    ClientAlreadyUpToDate(ClientId, Height, Height),

    #[error("the client on destination chain is at a higher height (client id: {0}, source height: {1}, dest height: {2})")]
    ClientAtHigherHeight(ClientId, Height, Height),

    #[error("transaction processing by modules failed")]
    TransactionFailed,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
