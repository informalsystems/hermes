//! Capabilities: this is a placeholder.

use crate::prelude::*;
use alloc::borrow::Cow;
use core::{fmt, str::FromStr};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct Capability {
    index: u64,
}

impl Capability {
    pub fn new(index: u64) -> Capability {
        Self { index }
    }

    pub fn index(&self) -> u64 {
        self.index
    }
}

impl Default for Capability {
    fn default() -> Self {
        Self::new(0)
    }
}

impl From<u64> for Capability {
    fn from(index: u64) -> Self {
        Self { index }
    }
}

#[derive(Debug, PartialEq)]
pub struct InvalidCapabilityName;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CapabilityName(String);

impl CapabilityName {
    pub fn new(s: Cow<'_, str>) -> Result<Self, InvalidCapabilityName> {
        if !s.trim().is_empty() {
            Ok(Self(s.into_owned()))
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
        Self::new(Cow::Borrowed(s))
    }
}
