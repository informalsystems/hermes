use super::error;
use anomaly::fail;
use serde_derive::{Deserialize, Serialize};

/// Type of the client, depending on the specific consensus algorithm.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ClientType {
    Tendermint = 1,
}

impl ClientType {
    /// Yields the identifier of this client type as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Tendermint => "tendermint",
        }
    }
}

impl std::str::FromStr for ClientType {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "tendermint" => Ok(Self::Tendermint),
            _ => fail!(error::Kind::UnknownClientType, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ClientType;
    use std::str::FromStr;

    #[test]
    fn parse_tendermint_client_type() {
        let client_type = ClientType::from_str("tendermint");

        match client_type {
            Ok(ClientType::Tendermint) => (),
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
