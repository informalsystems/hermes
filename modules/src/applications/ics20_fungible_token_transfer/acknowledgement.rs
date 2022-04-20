use super::error::Error;
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement as GenericAcknowledgement;
use crate::core::ics26_routing::context::Acknowledgement as AckTrait;
use crate::prelude::*;

use serde::Deserialize;

/// A string constant included in error acknowledgements.
/// NOTE: Changing this const is state machine breaking as acknowledgements are written into state
pub const ACK_ERR_STR: &str = "error handling packet on destination chain: see events for details";
pub const ACK_SUCCESS_B64: &[u8] = b"AQ==";

#[derive(Deserialize)]
pub enum Acknowledgement {
    /// Equivalent to b"AQ==" (i.e. `base64::encode(0x01)`)
    Success(Vec<u8>),
    /// Error Acknowledgement
    Error(String),
}

impl Acknowledgement {
    pub fn from_error(err: Error) -> Self {
        fn abci_info(_err: Error) -> usize {
            todo!()
        }
        Self::Error(format!("ABCI code: {}: {}", abci_info(err), ACK_ERR_STR))
    }
}

impl From<GenericAcknowledgement> for Acknowledgement {
    fn from(ack: GenericAcknowledgement) -> Self {
        if ack.as_ref() == ACK_SUCCESS_B64 {
            Self::Success(ACK_SUCCESS_B64.to_vec())
        } else {
            Self::Error(ACK_ERR_STR.to_owned())
        }
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

impl AckTrait for Acknowledgement {}
