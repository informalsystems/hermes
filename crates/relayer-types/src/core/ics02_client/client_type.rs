use serde_derive::{Deserialize, Serialize};
use std::fmt::{Display, Error as FmtError, Formatter};

use crate::clients::ics07_tendermint::TENDERMINT_CLIENT_TYPE;
use crate::clients::ics08_wasm::WASM_CLIENT_TYPE;

use super::error::Error;

/// Type of the client, depending on the specific consensus algorithm.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ClientType {
    /// ICS 07 Tendermint Client
    Tendermint = 7,

    /// ICS 08 Wasm Client
    Wasm = 8,
}

impl ClientType {
    /// Yields the identifier of this client type as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Tendermint => TENDERMINT_CLIENT_TYPE,
            Self::Wasm => WASM_CLIENT_TYPE,
        }
    }
}

impl Display for ClientType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "ClientType({})", self.as_str())
    }
}

impl core::str::FromStr for ClientType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            TENDERMINT_CLIENT_TYPE => Ok(Self::Tendermint),
            WASM_CLIENT_TYPE => Ok(Self::Wasm),

            _ => Err(Error::unknown_client_type(s.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;
    use test_log::test;

    use super::ClientType;
    use crate::core::ics02_client::error::{Error, ErrorDetail};

    #[test]
    fn parse_tendermint_client_type() {
        let client_type = ClientType::from_str("07-tendermint");

        match client_type {
            Ok(ClientType::Tendermint) => (),
            _ => panic!("parse failed"),
        }
    }

    #[test]
    fn parse_wasm_client_type() {
        let client_type = ClientType::from_str("08-wasm");

        match client_type {
            Ok(ClientType::Wasm) => (),
            _ => panic!("parse failed"),
        }
    }

    #[test]
    fn parse_unknown_client_type() {
        let client_type_str = "some-random-client-type";
        let result = ClientType::from_str(client_type_str);

        match result {
            Err(Error(ErrorDetail::UnknownClientType(e), _)) => {
                assert_eq!(&e.client_type, client_type_str)
            }
            _ => {
                panic!("Expected ClientType::from_str to fail with UnknownClientType, instead got",)
            }
        }
    }

    #[test]
    fn parse_tendermint_as_string_result() {
        let client_type = ClientType::Tendermint;
        let type_string = client_type.as_str();
        let client_type_from_str = ClientType::from_str(type_string).unwrap();
        assert_eq!(client_type_from_str, client_type);
    }

    #[test]
    fn parse_wasm_as_string_result() {
        let client_type = ClientType::Wasm;
        let type_string = client_type.as_str();
        let client_type_from_str = ClientType::from_str(type_string).unwrap();
        assert_eq!(client_type_from_str, client_type);
    }
}
