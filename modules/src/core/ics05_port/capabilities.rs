//! Capabilities: this is a placeholder.

use crate::prelude::*;
use alloc::borrow::Cow;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::{fmt, str::FromStr};

pub type PortCapability = TypedCapability<PortCapabilityType>;

pub type ChannelCapability = TypedCapability<ChannelCapabilityType>;

pub trait CapabilityMarker {}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct PortCapabilityType;

impl CapabilityMarker for PortCapabilityType {}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct ChannelCapabilityType;

impl CapabilityMarker for ChannelCapabilityType {}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct TypedCapability<T: CapabilityMarker>(Capability, PhantomData<T>);

impl<T: CapabilityMarker> Deref for TypedCapability<T> {
    type Target = Capability;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: CapabilityMarker> DerefMut for TypedCapability<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: CapabilityMarker> From<TypedCapability<T>> for Capability {
    fn from(cap: TypedCapability<T>) -> Self {
        cap.0
    }
}

impl<T: CapabilityMarker> From<Capability> for TypedCapability<T> {
    fn from(cap: Capability) -> Self {
        TypedCapability(cap, PhantomData)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
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
