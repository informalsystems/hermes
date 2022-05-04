use super::error::Error;
use crate::core::ics26_routing::context::Acknowledgement as AckTrait;
use crate::prelude::*;
use core::fmt::{Display, Formatter};

use serde::{Deserialize, Deserializer};

/// A string constant included in error acknowledgements.
/// NOTE: Changing this const is state machine breaking as acknowledgements are written into state
pub const ACK_ERR_STR: &str = "error handling packet on destination chain: see events for details";
pub const ACK_SUCCESS_B64: &[u8] = b"AQ==";

#[derive(Clone, Debug)]
pub enum Acknowledgement {
    /// Equivalent to b"AQ==" (i.e. `base64::encode(0x01)`)
    Success(Vec<u8>),
    /// Error Acknowledgement
    Error(String),
}

impl Acknowledgement {
    pub fn success() -> Self {
        Self::Success(ACK_SUCCESS_B64.to_vec())
    }

    pub fn from_error(err: Error) -> Self {
        Self::Error(format!("{}: {}", ACK_ERR_STR, err))
    }
}

impl AsRef<[u8]> for Acknowledgement {
    fn as_ref(&self) -> &[u8] {
        match self {
            Acknowledgement::Success(b) => b.as_slice(),
            Acknowledgement::Error(s) => s.as_bytes(),
        }
    }
}

impl<'de> Deserialize<'de> for Acknowledgement {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        let ack = if s.as_bytes() == ACK_SUCCESS_B64 {
            Self::Success(ACK_SUCCESS_B64.to_vec())
        } else {
            Self::Error(s)
        };
        Ok(ack)
    }
}

impl Display for Acknowledgement {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Acknowledgement::Success(_) => write!(f, "AQ=="),
            Acknowledgement::Error(err_str) => write!(f, "{}", err_str),
        }
    }
}

impl AckTrait for Acknowledgement {}
