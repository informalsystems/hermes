use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::try_from_raw::TryFromRaw;
use serde_derive::{Deserialize, Serialize};

// Import proto declarations.
use crate::ics24_host::error::ValidationError;
use ibc_proto::connection::{ConnectionEnd as RawConnectionEnd, Counterparty as RawCounterparty};
use std::convert::{TryFrom, TryInto};

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
        if value.id == "" {
            return Err(Kind::ConnectionNotFound.into());
        }

        Ok(Self::new(
            State::from_i32(value.state),
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Counterparty {
    client_id: ClientId,
    connection_id: ConnectionId,
    prefix: CommitmentPrefix,
}

// Converts from the wire format RawCounterparty. Typically used from the relayer side
// during queries for response validation and to extract the Counterparty structure.
impl TryFrom<RawCounterparty> for Counterparty {
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawCounterparty) -> Result<Self, Self::Error> {
        Ok(Counterparty::new(
            value
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            value
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            value
                .prefix
                .ok_or_else(|| Kind::MissingCounterparty)?
                .key_prefix
                .into(),
        )?)
    }
}

impl Counterparty {
    pub fn new(
        client_id: ClientId,
        connection_id: ConnectionId,
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
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
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

/// Function required by ICS 03. Returns the list of all possible versions that the connection
/// handshake protocol supports.
/// TODO: What are the precise values for the versions which this function returns? Perhaps encode the versions as constants.
pub fn get_compatible_versions() -> Vec<String> {
    vec!["test".to_string()]
}

/// Function required by ICS 03. Returns one version out of the supplied list of versions, which the
/// connection handshake protocol prefers.
/// TODO: Fix this with proper code.
pub fn pick_version(candidates: Vec<String>) -> Option<String> {
    let selection: String = candidates
        .get(0)
        .unwrap_or(&String::from("none"))
        .to_string();
    Some(selection)
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
