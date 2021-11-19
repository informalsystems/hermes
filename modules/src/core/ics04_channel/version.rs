use serde_derive::{Deserialize, Serialize};

use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Version(String);

impl From<Version> for String {
    fn from(domain_version: Version) -> Self {
        domain_version.0
    }
}

impl From<String> for Version {
    fn from(raw_version: String) -> Self {
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
