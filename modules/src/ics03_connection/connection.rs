use std::convert::{TryFrom, TryInto};
use std::str::FromStr;

use ibc_proto::ibc::core::connection::v1::{
    ConnectionEnd as RawConnectionEnd, Counterparty as RawCounterparty,
};
use tendermint_proto::DomainType;

use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::error::ValidationError;
use crate::ics24_host::identifier::{ClientId, ConnectionId};

#[derive(Clone, Debug, PartialEq)]
pub struct ConnectionEnd {
    state: State,
    client_id: ClientId,
    counterparty: Counterparty,
    versions: Vec<String>,
}

impl DomainType<RawConnectionEnd> for ConnectionEnd {}

impl TryFrom<RawConnectionEnd> for ConnectionEnd {
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawConnectionEnd) -> Result<Self, Self::Error> {
        Ok(Self::new(
            value.state.try_into()?,
            value
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            value
                .counterparty
                .ok_or_else(|| Kind::MissingCounterparty)?
                .try_into()?,
            value.versions,
        )?)
    }
}

impl From<ConnectionEnd> for RawConnectionEnd {
    fn from(value: ConnectionEnd) -> Self {
        RawConnectionEnd {
            client_id: value.client_id.to_string(),
            versions: value.versions,
            state: value.state as i32,
            counterparty: Some(RawCounterparty::from(value.counterparty)),
        }
    }
}

impl ConnectionEnd {
    pub fn new(
        state: State,
        client_id: ClientId,
        counterparty: Counterparty,
        versions: Vec<String>, // TODO: Use Newtype for aliasing the version to a string
    ) -> Result<Self, Error> {
        Ok(Self {
            state,
            client_id,
            counterparty,
            versions: validate_versions(versions).map_err(|e| Kind::InvalidVersion.context(e))?,
        })
    }

    /// Setter for the `state` field.
    pub fn set_state(&mut self, new_state: State) {
        self.state = new_state;
    }

    /// Setter for the `version` field.
    /// TODO: A ConnectionEnd should only store one version.
    pub fn set_version(&mut self, new_version: String) {
        self.versions.insert(0, new_version)
    }

    /// Helper function to compare the counterparty of this end with another counterparty.
    pub fn counterparty_matches(&self, other: &Counterparty) -> bool {
        self.counterparty.eq(other)
    }

    /// Helper function to compare the client id of this end with another client identifier.
    pub fn client_id_matches(&self, other: &ClientId) -> bool {
        self.client_id.eq(other)
    }

    /// Helper function to compare the state of this end with another state.
    pub fn state_matches(&self, other: &State) -> bool {
        self.state.eq(other)
    }

    /// Getter for the state of this connection end.
    pub fn state(&self) -> &State {
        &self.state
    }

    /// Getter for the client id on the local party of this connection end.
    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    /// Getter for the list of versions in this connection end.
    pub fn versions(&self) -> Vec<String> {
        self.versions.clone()
    }

    /// Getter for the counterparty. Returns a `clone()`.
    pub fn counterparty(&self) -> Counterparty {
        self.counterparty.clone()
    }

    /// TODO: Clean this up, probably not necessary.
    pub fn validate_basic(&self) -> Result<(), ValidationError> {
        self.counterparty.validate_basic()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Counterparty {
    client_id: ClientId,
    connection_id: Option<ConnectionId>,
    prefix: CommitmentPrefix,
}

// Converts from the wire format RawCounterparty. Typically used from the relayer side
// during queries for response validation and to extract the Counterparty structure.
impl TryFrom<RawCounterparty> for Counterparty {
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawCounterparty) -> Result<Self, Self::Error> {
        let connection_id = Some(value.connection_id)
            .filter(|x| !x.is_empty())
            .map(|v| FromStr::from_str(v.as_str()))
            .transpose()
            .map_err(|e| Kind::IdentifierError.context(e))?;
        Ok(Counterparty::new(
            value
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            connection_id,
            value
                .prefix
                .ok_or_else(|| Kind::MissingCounterparty)?
                .key_prefix
                .into(),
        )?)
    }
}

impl From<Counterparty> for RawCounterparty {
    fn from(value: Counterparty) -> Self {
        RawCounterparty {
            client_id: value.client_id.as_str().to_string(),
            connection_id: value
                .connection_id
                .map_or_else(|| "".to_string(), |v| v.as_str().to_string()),
            prefix: Some(ibc_proto::ibc::core::commitment::v1::MerklePrefix {
                key_prefix: value.prefix.0,
            }),
        }
    }
}

impl Counterparty {
    pub fn new(
        client_id: ClientId,
        connection_id: Option<ConnectionId>,
        prefix: CommitmentPrefix,
    ) -> Result<Self, Error> {
        Ok(Self {
            client_id,
            connection_id,
            prefix,
        })
    }

    /// Getter for the client id.
    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    /// Getter for connection id.
    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.connection_id.as_ref()
    }

    pub fn prefix(&self) -> &CommitmentPrefix {
        &self.prefix
    }

    pub fn validate_basic(&self) -> Result<(), ValidationError> {
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

#[derive(Clone, Debug, PartialEq)]
pub enum State {
    Init = 1,
    TryOpen = 2,
    Open = 3,
}

impl State {
    /// Yields the State as a string.
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Init => "INIT",
            Self::TryOpen => "TRYOPEN",
            Self::Open => "OPEN",
        }
    }
}

impl TryFrom<i32> for State {
    type Error = anomaly::Error<Kind>;
    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Init),
            2 => Ok(Self::TryOpen),
            3 => Ok(Self::Open),
            _ => Err(Kind::InvalidState(value).into()),
        }
    }
}

impl From<State> for i32 {
    fn from(value: State) -> Self {
        value.into()
    }
}
