use anomaly::{BoxError, Context};
use thiserror::Error;

pub type ValidationError = anomaly::Error<ValidationKind>;

#[derive(Clone, Debug, Error)]
pub enum ValidationKind {
    #[error("identifier {id} cannot contain separator '/'")]
    ContainsSeparator { id: String },

    #[error("identifier {id} has invalid length {length} must be between {min}-{max} characters")]
    InvalidLength {
        id: String,
        length: usize,
        min: usize,
        max: usize,
    },

    #[error("identifier {id} must only contain alphanumeric characters or `.`, `_`, `+`, `-`, `#`, - `[`, `]`, `<`, `>`")]
    InvalidCharacter { id: String },

    #[error("identifier cannot be empty")]
    Empty,

    #[error("chain identifiers are expected to be in epoch format {id}")]
    ChainIdInvalidFormat { id: String },
}

impl ValidationKind {
    pub fn contains_separator(id: String) -> Self {
        Self::ContainsSeparator { id }
    }

    pub fn invalid_length(id: String, length: usize, min: usize, max: usize) -> Self {
        Self::InvalidLength {
            id,
            length,
            min,
            max,
        }
    }

    pub fn invalid_character(id: String) -> Self {
        Self::InvalidCharacter { id }
    }

    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn chain_id_invalid_format(id: String) -> Self {
        Self::ChainIdInvalidFormat { id }
    }

    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
