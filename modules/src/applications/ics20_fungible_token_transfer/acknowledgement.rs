use super::error::Error;
use crate::core::ics26_routing::context::Acknowledgement as AckTrait;
use crate::prelude::*;

use serde::{Deserialize, Deserializer};

/// A string constant included in error acknowledgements.
/// NOTE: Changing this const is state machine breaking as acknowledgements are written into state
pub const ACK_ERR_STR: &str = "error handling packet on destination chain: see events for details";
pub const ACK_SUCCESS_B64: &[u8] = b"AQ==";

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
        fn abci_info(_err: Error) -> usize {
            todo!()
        }
        Self::Error(format!("ABCI code: {}: {}", abci_info(err), ACK_ERR_STR))
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

impl AckTrait for Acknowledgement {}
