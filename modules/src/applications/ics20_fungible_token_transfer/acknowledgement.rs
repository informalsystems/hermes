use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement as GenericAcknowledgement;
use crate::core::ics26_routing::context::Acknowledgement as AckTrait;
use crate::prelude::*;

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
    pub fn error() -> Self {
        Self::Error(ACK_ERR_STR.to_owned())
    }
}

impl From<GenericAcknowledgement> for Acknowledgement {
    fn from(ack: GenericAcknowledgement) -> Self {
        if ack.as_ref() == ACK_SUCCESS_B64 {
            Self::Success(ack.into_bytes())
        } else {
            Self::error()
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

impl AckTrait for Acknowledgement {
    fn success(&self) -> bool {
        matches!(self, Self::Success(_))
    }
}
