use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::try_from_raw::TryFromRaw;
use serde_derive::{Deserialize, Serialize};

// Import proto declarations.
use anomaly::fail;
use ibc_proto::connection::ConnectionEnd as RawConnectionEnd;
use ibc_proto::connection::Counterparty as RawCounterparty;
use std::convert::TryFrom;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionEnd {
    state: State,
    client_id: ClientId,
    counterparty: Counterparty,
    versions: Vec<String>,
}

impl TryFromRaw for ConnectionEnd {
    type RawType = RawConnectionEnd;
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawConnectionEnd) -> Result<Self, Self::Error> {
        // Todo: Is validation complete here? (Code was moved from `from_proto_connection_end`.)
        if value.id == "" {
            return Err(Kind::ConnectionNotFound.into());
        }

        // The Counterparty field is an Option, may be missing.
        match value.counterparty {
            Some(cp) => {
                let mut conn = ConnectionEnd::new(
                    value
                        .client_id
                        .parse()
                        .map_err(|e| Kind::IdentifierError.context(e))?,
                    Counterparty::try_from(cp)?,
                    value.versions,
                )
                .unwrap();

                // Set the state.
                conn.set_state(State::from_i32(value.state));
                Ok(conn)
            }

            // If no counterparty was set, signal the error.
            None => Err(Kind::MissingCounterparty.into()),
        }
    }
}

impl ConnectionEnd {
    pub fn new(
        client_id: ClientId,
        counterparty: Counterparty,
        versions: Vec<String>,
    ) -> Result<Self, Error> {
        Ok(Self {
            state: State::Uninitialized,
            client_id,
            counterparty,
            versions: validate_versions(versions).map_err(|e| Kind::InvalidVersion.context(e))?,
        })
    }

    pub fn set_state(&mut self, new_state: State) {
        self.state = new_state;
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn client_id(&self) -> String {
        self.client_id.as_str().into()
    }

    pub fn counterparty(&self) -> Counterparty {
        self.counterparty.clone()
    }

    pub fn versions(&self) -> Vec<String> {
        self.versions.clone()
    }

    fn validate_basic(&self) -> Result<(), Error> {
        self.counterparty().validate_basic()
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Counterparty {
    client_id: ClientId,
    connection_id: ConnectionId,
    prefix: CommitmentPrefix,
}

impl TryFrom<RawCounterparty> for Counterparty {
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawCounterparty) -> Result<Self, Self::Error> {
        // Todo: Is validation complete here? (code was moved from `from_proto_counterparty`)
        match value.prefix {
            Some(prefix) => Counterparty::new(
                value.client_id,
                value.connection_id,
                CommitmentPrefix::new(prefix.key_prefix),
            ),
            None => Err(Kind::MissingCounterpartyPrefix.into()),
        }
    }
}

impl Counterparty {
    pub fn new(
        client_id: String,
        connection_id: String,
        prefix: CommitmentPrefix,
    ) -> Result<Self, Error> {
        Ok(Self {
            client_id: client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            prefix,
        })
    }

    pub fn client_id(&self) -> String {
        self.client_id.as_str().into()
    }

    pub fn connection_id(&self) -> String {
        self.connection_id.as_str().into()
    }

    pub fn prefix(&self) -> &CommitmentPrefix {
        &self.prefix
    }

    pub fn validate_basic(&self) -> Result<(), Error> {
        Ok(())
    }
}

pub fn validate_versions(versions: Vec<String>) -> Result<Vec<String>, String> {
    let v: Vec<String> = versions.to_vec();
    if v.is_empty() {
        return Err("missing versions".to_string());
    }

    for v in versions.into_iter() {
        validate_version(v)?;
    }
    Ok(v)
}

pub fn validate_version(version: String) -> Result<String, String> {
    if version.trim().is_empty() {
        return Err("empty version string".to_string());
    }
    Ok(version)
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum State {
    Uninitialized = 0,
    Init,
    TryOpen,
    Open,
}

impl State {
    /// Yields the State as a string.
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Uninitialized => "UNINITIALIZED",
            Self::Init => "INIT",
            Self::TryOpen => "TRYOPEN",
            Self::Open => "OPEN",
        }
    }

    /// Parses the State from a i32.
    pub fn from_i32(nr: i32) -> Self {
        match nr {
            1 => Self::Init,
            2 => Self::TryOpen,
            3 => Self::Open,
            _ => Self::Uninitialized,
        }
    }
}

impl std::str::FromStr for State {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "UNINITIALIZED" => Ok(Self::Uninitialized),
            "INIT" => Ok(Self::Init),
            "TRYOPEN" => Ok(Self::TryOpen),
            "OPEN" => Ok(Self::Open),
            _ => fail!(Kind::UnknownState, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    #[test]
    fn parse_connection_state() {
        use super::State;

        struct Test {
            state: &'static str,
            want_res: State,
            want_err: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                state: "UNINITIALIZED",
                want_res: State::Uninitialized,
                want_err: false,
            },
            Test {
                state: "INIT",
                want_res: State::Init,
                want_err: false,
            },
            Test {
                state: "TRYOPEN",
                want_res: State::TryOpen,
                want_err: false,
            },
            Test {
                state: "OPEN",
                want_res: State::Open,
                want_err: false,
            },
            Test {
                state: "INVALID_STATE",
                want_res: State::Open,
                want_err: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            match State::from_str(test.state) {
                Ok(res) => {
                    assert!(!test.want_err);
                    assert_eq!(test.want_res, res);
                }
                Err(_) => assert!(test.want_err, "parse failed"),
            }
        }
    }
}
