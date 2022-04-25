use core::str::FromStr;

use derive_more::Display;
use serde::{Deserialize, Serialize};
use subtle_encoding::bech32;

use super::error::Error;
use crate::prelude::*;

/// A type representing a valid `bech32` address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Display)]
pub struct Address(String);

impl FromStr for Address {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_string();
        if s.trim().is_empty() {
            return Err(Error::empty_signer());
        }

        let _ = bech32::decode(s.as_str()).map_err(Error::address_not_valid_bech32)?;

        Ok(Self(s))
    }
}

impl AsRef<str> for Address {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}
