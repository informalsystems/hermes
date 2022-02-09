//! Capabilities: this is a placeholder.

use crate::prelude::*;
use core::{fmt, str::FromStr};

#[derive(Clone, Debug, PartialEq)]
pub struct Capability {
    index: u64,
}

impl Capability {
    pub fn new() -> Capability {
        Self { index: 0x0 }
    }

    pub fn index(&self) -> u64 {
        self.index
    }
}

impl Default for Capability {
    fn default() -> Self {
        Self::new()
    }
}

impl From<u64> for Capability {
    fn from(index: u64) -> Self {
        Self { index }
    }
}

#[derive(Debug, PartialEq)]
pub struct InvalidCapabilityName;

#[derive(Clone, Debug, PartialEq)]
pub struct CapabilityName(String);

impl CapabilityName {
    pub fn new(s: impl AsRef<str>) -> Result<Self, InvalidCapabilityName> {
        let s = s.as_ref().trim();
        if !s.is_empty() {
            Ok(Self(s.to_owned()))
        } else {
            Err(InvalidCapabilityName)
        }
    }
}

impl fmt::Display for CapabilityName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for CapabilityName {
    type Err = InvalidCapabilityName;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}
