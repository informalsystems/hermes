use super::exported::*;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use serde_derive::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionEnd {
    state: State,
    client_id: ClientId,
    counterparty: Counterparty,
    versions: Vec<String>,
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
}

impl Connection for ConnectionEnd {
    type ValidationError = Error;

    fn state(&self) -> &State {
        &self.state
    }

    fn client_id(&self) -> String {
        self.client_id.as_str().into()
    }

    fn counterparty(
        &self,
    ) -> Box<dyn ConnectionCounterparty<ValidationError = Self::ValidationError>> {
        Box::new(self.counterparty.clone())
    }

    fn versions(&self) -> Vec<String> {
        self.versions.clone()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.counterparty().validate_basic()
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Counterparty {
    client_id: ClientId,
    connection_id: ConnectionId,
    prefix: CommitmentPrefix,
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
}

impl ConnectionCounterparty for Counterparty {
    type ValidationError = Error;

    fn client_id(&self) -> String {
        self.client_id.as_str().into()
    }

    fn connection_id(&self) -> String {
        self.connection_id.as_str().into()
    }

    fn prefix(&self) -> &CommitmentPrefix {
        &self.prefix
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // todo!()
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
