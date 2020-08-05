use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics24_host::identifier::ClientId;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("unknown client type")]
    UnknownClientType,

    #[error("client already exists: {0}")]
    ClientAlreadyExists(ClientId),

    #[error("client not found: {0}")]
    ClientNotFound(ClientId),

    #[error("implementation specific")]
    ImplementationSpecific,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
