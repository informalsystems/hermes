//! Configuration-related types.
//!
//! Implements defaults, as well as serializing and
//! deserializing with upper-bound verification.

use serde::de::Unexpected;
use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

const DEFAULT_MAX_MSG_NUM: usize = 30;
const DEFAULT_MAX_TX_SIZE: usize = 2 * 1048576; // 2 MBytes

const BOUND_MAX_MSG_NUM: usize = 100;
const BOUND_MAX_TX_SIZE: usize = 8 * 1048576; // 8 MBytes

#[derive(Debug, Clone, Copy)]
pub struct MaxMsgNum(usize);

impl Default for MaxMsgNum {
    fn default() -> Self {
        Self(DEFAULT_MAX_MSG_NUM)
    }
}

impl<'de> Deserialize<'de> for MaxMsgNum {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let u = usize::deserialize(deserializer)?;

        if u > BOUND_MAX_MSG_NUM {
            return Err(D::Error::invalid_value(
                Unexpected::Unsigned(u as u64),
                &format!("a usize less than {}", BOUND_MAX_MSG_NUM).as_str(),
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
        self.0.to_string().serialize(serializer)
    }
}

impl From<MaxMsgNum> for usize {
    fn from(m: MaxMsgNum) -> Self {
        m.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MaxTxSize(usize);

impl Default for MaxTxSize {
    fn default() -> Self {
        Self(DEFAULT_MAX_TX_SIZE)
    }
}

impl<'de> Deserialize<'de> for MaxTxSize {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let u = usize::deserialize(deserializer)?;

        if u > BOUND_MAX_TX_SIZE {
            return Err(D::Error::invalid_value(
                Unexpected::Unsigned(u as u64),
                &format!("a usize less than {}", BOUND_MAX_TX_SIZE).as_str(),
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
        self.0.to_string().serialize(serializer)
    }
}

impl From<MaxTxSize> for usize {
    fn from(m: MaxTxSize) -> Self {
        m.0
    }
}
