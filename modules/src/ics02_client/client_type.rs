use super::error;
use serde_derive::{Deserialize, Serialize};

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
            Self::Tendermint => "Tendermint",

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock => "mock",
        }
    }
}

impl std::str::FromStr for ClientType {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Tendermint" => Ok(Self::Tendermint),

            #[cfg(any(test, feature = "mocks"))]
            "mock" => Ok(Self::Mock),

            _ => Err(error::Kind::UnknownClientType(s.to_string()).into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ClientType;
    use std::str::FromStr;

    #[test]
    fn parse_tendermint_client_type() {
        let client_type = ClientType::from_str("Tendermint");

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
