//! Configuration-related types.
//!
//! Implements defaults, as well as serializing and
//! deserializing with upper-bound verification.

use core::fmt;

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

/// A memo domain-type.
///
/// Hermes uses this type to populate the `tx.memo` field for
/// each transaction it submits.
/// The memo can be configured on a per-chain basis.
///
#[derive(Clone, Debug, Default)]
pub struct Memo(String);

impl Memo {
    const MAX_LEN: usize = 50;

    pub fn apply_suffix(&mut self, suffix: &str) {
        // Add a separator if the memo
        // is pre-populated with some content already.
        if !self.0.is_empty() {
            self.0.push_str(" | ");
        }

        self.0.push_str(suffix);
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for Memo {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let m = String::deserialize(deserializer)?;

        if m.len() > Self::MAX_LEN {
            return Err(D::Error::invalid_length(
                m.len(),
                &format!("a string length of at most {}", Self::MAX_LEN).as_str(),
            ));
        }

        Ok(Memo(m))
    }
}

impl Serialize for Memo {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl fmt::Display for Memo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
