use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics24_host::identifier::ClientId;
use crate::Height;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("unknown client type")]
    UnknownClientType,

    #[error("client already exists: {0}")]
    ClientAlreadyExists(ClientId),

    #[error("client not found: {0}")]
    ClientNotFound(ClientId),

    #[error("consensus state not found at: {0} at height {1}")]
    ConsensusStateNotFound(ClientId, Height),

    #[error("implementation specific")]
    ImplementationSpecific,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
