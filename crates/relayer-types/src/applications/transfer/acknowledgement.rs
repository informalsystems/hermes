use core::fmt::{Display, Error as FmtError, Formatter};

use serde::{Deserialize, Serialize};

use crate::prelude::*;

use super::error::Error;

/// A string constant included in error acknowledgements.
/// NOTE: Changing this const is state machine breaking as acknowledgements are written into state
pub const ACK_ERR_STR: &str = "error handling packet on destination chain: see events for details";

/// A successful acknowledgement, equivalent to `base64::encode(0x01)`.
pub const ACK_SUCCESS_B64: &str = "AQ==";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstAckSuccess {
    #[serde(rename = "AQ==")]
    Success,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Acknowledgement {
    /// Successful Acknowledgement
    /// e.g. `{"result":"AQ=="}`
    #[serde(rename = "result")]
    Success(ConstAckSuccess),
    /// Error Acknowledgement
    /// e.g. `{"error":"cannot unmarshal ICS-20 transfer packet data"}`
    #[serde(rename = "error")]
    Error(String),
}

impl Acknowledgement {
    pub fn success() -> Self {
        Self::Success(ConstAckSuccess::Success)
    }

    pub fn from_error(err: Error) -> Self {
        Self::Error(format!("{ACK_ERR_STR}: {err}"))
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            Acknowledgement::Success(_) => write!(f, "{ACK_SUCCESS_B64}"),
            Acknowledgement::Error(err_str) => write!(f, "{err_str}"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_ack_ser() {
        fn ser_json_assert_eq(ack: Acknowledgement, json_str: &str) {
            let ser = serde_json::to_string(&ack).unwrap();
            assert_eq!(ser, json_str)
        }

        ser_json_assert_eq(Acknowledgement::success(), r#"{"result":"AQ=="}"#);
        ser_json_assert_eq(
            Acknowledgement::Error("cannot unmarshal ICS-20 transfer packet data".to_owned()),
            r#"{"error":"cannot unmarshal ICS-20 transfer packet data"}"#,
        );
    }

    #[test]
    fn test_ack_de() {
        fn de_json_assert_eq(json_str: &str, ack: Acknowledgement) {
            let de = serde_json::from_str::<Acknowledgement>(json_str).unwrap();
            assert_eq!(de, ack)
        }

        de_json_assert_eq(r#"{"result":"AQ=="}"#, Acknowledgement::success());
        de_json_assert_eq(
            r#"{"error":"cannot unmarshal ICS-20 transfer packet data"}"#,
            Acknowledgement::Error("cannot unmarshal ICS-20 transfer packet data".to_owned()),
        );

        assert!(serde_json::from_str::<Acknowledgement>(r#"{"result":"AQ="}"#).is_err());
        assert!(serde_json::from_str::<Acknowledgement>(r#"{"success":"AQ=="}"#).is_err());
    }
}
