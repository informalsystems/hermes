use super::exported::*;
use crate::ics03_connection::error;
use crate::ics03_connection::error::Kind;
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
    pub fn new(client_id: ClientId, counterparty: Counterparty, versions: Vec<String>) -> Self {
        ConnectionEnd {
            state: State::Uninitialized,
            client_id,
            counterparty,
            versions,
        }
    }
}

impl ConnectionI for ConnectionEnd {
    type ValidationError = error::Error;

    fn state(&self) -> State {
        self.state.clone()
    }

    fn client_id(&self) -> String {
        String::from(self.client_id.as_str())
    }

    fn counterparty(&self) -> Box<dyn CounterpartyI<ValidationError = Self::ValidationError>> {
        Box::new(self.counterparty.clone())
    }

    fn versions(&self) -> Vec<String> {
        self.versions.clone()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        if self.versions.len() == 0 {
            return Err(error::Kind::InvalidVersion
                .context("missing connection versions")
                .into());
        }

        for v in self.versions().iter() {
            if v.trim().to_string() == String::from("") {
                return Err(error::Kind::InvalidVersion
                    .context("empty version string")
                    .into());
            }
        }
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
        prefix: CommitmentPrefix
    ) -> Result<Self, error::Error> {
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

impl CounterpartyI for Counterparty {
    type ValidationError = error::Error;

    fn client_id(&self) -> String {
        String::from(self.client_id.as_str())
    }

    fn connection_id(&self) -> String {
        String::from(self.connection_id.as_str())
    }

    fn prefix(&self) -> CommitmentPrefix {
        self.prefix.clone()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        todo!()
    }
}
