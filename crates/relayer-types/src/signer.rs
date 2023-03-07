use core::str::FromStr;

use derive_more::Display;
use flex_error::define_error;
use serde::{Deserialize, Serialize};

use crate::prelude::*;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    SignerError {
        EmptySigner
            | _ | { "signer cannot be empty" },
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Display)]
pub struct Signer(String);

impl Signer {
    pub fn dummy() -> Self {
        Self("cosmos000000000000000000000000000000000000000".to_string())
    }
}

impl FromStr for Signer {
    type Err = SignerError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_string();
        if s.trim().is_empty() {
            return Err(SignerError::empty_signer());
        }
        Ok(Self(s))
    }
}

impl AsRef<str> for Signer {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}
