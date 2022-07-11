use core::fmt::{Display, Formatter};

use serde::{Deserialize, Serialize};

use super::error::Error;
use crate::core::ics26_routing::context::Acknowledgement as AckTrait;
use crate::prelude::*;

/// A string constant included in error acknowledgements.
/// NOTE: Changing this const is state machine breaking as acknowledgements are written into state
pub const ACK_ERR_STR: &str = "error handling packet on destination chain: see events for details";

/// A successful acknowledgement, equivalent to `base64::encode(0x01)`.
pub const ACK_SUCCESS_B64: &str = "AQ==";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum ConstAckSuccess {
    #[serde(rename = "AQ==")]
    Success,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Acknowledgement {
    /// Successful Acknowledgement
    /// e.g. `{"result":"AQ=="}`
    #[serde(rename = "result")]
    Success(ConstAckSuccess),
    /// Error Acknowledgement
    /// e.g. `{"error":"cannot unmarshal ICS-20 transfer packet data"}`
    Error(String),
}

impl Acknowledgement {
    pub fn success() -> Self {
        Self::Success(ConstAckSuccess::Success)
    }

    pub fn from_error(err: Error) -> Self {
        Self::Error(format!("{}: {}", ACK_ERR_STR, err))
    }
}

impl AsRef<[u8]> for Acknowledgement {
    fn as_ref(&self) -> &[u8] {
        match self {
            Acknowledgement::Success(_) => ACK_SUCCESS_B64.as_bytes(),
            Acknowledgement::Error(s) => s.as_bytes(),
        }
    }
}

impl Display for Acknowledgement {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Acknowledgement::Success(_) => write!(f, "{}", ACK_SUCCESS_B64),
            Acknowledgement::Error(err_str) => write!(f, "{}", err_str),
        }
    }
}

impl AckTrait for Acknowledgement {}
