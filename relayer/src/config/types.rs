//! Configuration-related types.
//!
//! Implements defaults, as well as serializing and
//! deserializing with upper-bound verification.

use serde::de::Unexpected;
use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

#[derive(Debug, Clone, Copy)]
pub struct MaxMsgNum(usize);

impl MaxMsgNum {
    const DEFAULT: usize = 30;
    const MAX_BOUND: usize = 100;
}

impl Default for MaxMsgNum {
    fn default() -> Self {
        Self(Self::DEFAULT)
    }
}

impl<'de> Deserialize<'de> for MaxMsgNum {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let u = usize::deserialize(deserializer)?;

        if u > Self::MAX_BOUND {
            return Err(D::Error::invalid_value(
                Unexpected::Unsigned(u as u64),
                &format!("a usize less than {}", Self::MAX_BOUND).as_str(),
            ));
        }

        Ok(MaxMsgNum(u))
    }
}

impl Serialize for MaxMsgNum {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl From<MaxMsgNum> for usize {
    fn from(m: MaxMsgNum) -> Self {
        m.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MaxTxSize(usize);

impl MaxTxSize {
    const DEFAULT: usize = 2 * 1048576; // 2 MBytes
    const MAX_BOUND: usize = 8 * 1048576; // 8 MBytes
}

impl Default for MaxTxSize {
    fn default() -> Self {
        Self(Self::DEFAULT)
    }
}

impl<'de> Deserialize<'de> for MaxTxSize {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let u = usize::deserialize(deserializer)?;

        if u > Self::MAX_BOUND {
            return Err(D::Error::invalid_value(
                Unexpected::Unsigned(u as u64),
                &format!("a usize less than {}", Self::MAX_BOUND).as_str(),
            ));
        }

        Ok(MaxTxSize(u))
    }
}

impl Serialize for MaxTxSize {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl From<MaxTxSize> for usize {
    fn from(m: MaxTxSize) -> Self {
        m.0
    }
}
