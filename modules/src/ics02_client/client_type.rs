use std::fmt;

use serde_derive::{Deserialize, Serialize};

use super::error;

/// Type of the client, depending on the specific consensus algorithm.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ClientType {
    Tendermint = 1,

    #[cfg(any(test, feature = "mocks"))]
    Mock = 9999,
}

impl ClientType {
    /// Yields the identifier of this client type as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Tendermint => "07-tendermint",

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock => "9999-mock",
        }
    }
}

impl fmt::Display for ClientType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ClientType({})", self.as_string())
    }
}

impl std::str::FromStr for ClientType {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "07-tendermint" => Ok(Self::Tendermint),

            #[cfg(any(test, feature = "mocks"))]
            "mock" => Ok(Self::Mock),

            _ => Err(error::unknown_client_type_error(s.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use test_env_log::test;

    use super::ClientType;

    #[test]
    fn parse_tendermint_client_type() {
        let client_type = ClientType::from_str("07-tendermint");

        match client_type {
            Ok(ClientType::Tendermint) => (),
            _ => panic!("parse failed"),
        }
    }

    #[test]
    fn parse_mock_client_type() {
        let client_type = ClientType::from_str("mock");

        match client_type {
            Ok(ClientType::Mock) => (),
            _ => panic!("parse failed"),
        }
    }

    #[test]
    fn parse_unknown_client_type() {
        let client_type = ClientType::from_str("some-random-client-type");

        match client_type {
            Err(err) => assert_eq!(
                format!("{}", err),
                "unknown client type: some-random-client-type"
            ),
            _ => panic!("parse didn't fail"),
        }
    }
}
