//! Data type definition and utilities for the
//! version field of a channel end.
//!

use core::fmt;
use serde_derive::{Deserialize, Serialize};

use crate::applications::ics20_fungible_token_transfer;
use crate::prelude::*;

/// The version field for a `ChannelEnd`.
///
/// This field is opaque to the core IBC protocol.
/// No explicit validation is necessary, and the
/// spec (v1) currently allows empty strings.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Version(String);

impl Version {
    pub fn ics20() -> Self {
        Self(ics20_fungible_token_transfer::VERSION.to_string())
    }

    pub fn empty() -> Self {
        Self("".to_string())
    }
}

impl From<Version> for String {
    fn from(domain_version: Version) -> Self {
        domain_version.0
    }
}

impl From<String> for Version {
    fn from(raw_version: String) -> Self {
        // Version validation: nothing specific.
        Self(raw_version)
    }
}

impl From<&str> for Version {
    fn from(raw_version: &str) -> Self {
        Self(raw_version.into())
    }
}

/// The default version is empty (unspecified).
impl Default for Version {
    fn default() -> Self {
        Version::empty()
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
