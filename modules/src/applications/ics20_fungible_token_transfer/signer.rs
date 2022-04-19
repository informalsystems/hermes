use core::str::FromStr;

use derive_more::Display;
use serde::{Deserialize, Serialize};

use super::error::Error;
use crate::prelude::*;

/// This type is distinct from the `crate::signer::Signer` type as it is opaque to IBC, and it is
/// upto the corresponding chains to interpret it as they like.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Display)]
pub struct Signer(String);

impl FromStr for Signer {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_string();
        if s.trim().is_empty() {
            Err(Error::empty_signer())
        } else {
            Ok(Self(s))
        }
    }
}

impl AsRef<str> for Signer {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}
