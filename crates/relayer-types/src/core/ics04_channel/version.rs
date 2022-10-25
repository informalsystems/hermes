//! Data type definition and utilities for the
//! version field of a channel end.
//!

use core::convert::Infallible;
use core::fmt::{Display, Error as FmtError, Formatter};
use core::str::FromStr;
use serde_derive::{Deserialize, Serialize};
use serde_json as json;

use crate::applications::transfer;
use crate::prelude::*;

/// The version field for a `ChannelEnd`.
///
/// This field is opaque to the core IBC protocol.
/// No explicit validation is necessary, and the
/// spec (v1) currently allows empty strings.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Version(pub String);

impl Version {
    pub fn new(v: String) -> Self {
        Self(v)
    }

    pub fn ics20() -> Self {
        Self::new(transfer::VERSION.to_string())
    }

    pub fn ics20_with_fee() -> Self {
        let val = json::json!({
            "fee_version": "ics29-1",
            "app_version": transfer::VERSION,
        });

        Self::new(val.to_string())
    }

    pub fn empty() -> Self {
        Self::new("".to_string())
    }

    pub fn supports_fee(&self) -> bool {
        json::from_str::<json::Value>(&self.0)
            .ok()
            .and_then(|val| {
                let _app_version = val.get("app_version")?.as_str()?;

                let fee_version = val.get("fee_version")?.as_str()?;

                Some(fee_version == "ics29-1")
            })
            .unwrap_or(false)
    }
}

impl From<String> for Version {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl FromStr for Version {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s.to_string()))
    }
}

/// The default version is empty (unspecified).
impl Default for Version {
    fn default() -> Self {
        Version::empty()
    }
}

impl Display for Version {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod test {
    use super::Version;

    #[test]
    fn test_ics29_version() {
        {
            let version = Version::ics20();
            assert!(!version.supports_fee());
        }

        {
            let version = Version::ics20_with_fee();
            assert!(version.supports_fee());
        }
    }
}
