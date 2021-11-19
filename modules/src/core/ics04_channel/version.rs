//! Data type definition and utilities for the
//! version field of a channel end.
//!

use serde_derive::{Deserialize, Serialize};

use crate::prelude::*;

/// The version field for a `ChannelEnd`.
///
/// This field is opaque to the core IBC protocol.
/// No explicit validation is necessary, and the
/// spec (v1) currently allows empty strings.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Version(String);

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
        Self {
            0: raw_version.into(),
        }
    }
}

impl Default for Version {
    fn default() -> Self {
        Version("".to_string())
    }
}
