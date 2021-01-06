use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum Kind {
    #[error("invalid raw merkle proof")]
    InvalidRawMerkleProof,

    #[error("cannot apply an empty prefix")]
    EmptyPrefix,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
