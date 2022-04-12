//! Capabilities: this is a placeholder.

use crate::prelude::*;
use alloc::borrow::Cow;
use core::{fmt, str::FromStr};

pub trait Capability {
    fn index(&self) -> u64;
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
