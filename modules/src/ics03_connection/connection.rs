use super::exported::*;
use crate::ics03_connection::error;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use serde_derive::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConnectionEnd {
    state: State,
    client_id: ClientId,
    counterparty: Counterparty,
    version: String,
}

impl ConnectionEnd {
    pub fn new(
        state: ConnectionState,
        client_id: ClientId,
        counterparty: Counterparty,
        version: String,
    ) -> Self {
        ConnectionEnd {
            state,
            client_id,
            counterparty,
            version,
        }
    }
}

impl ConnectionI for ConnectionEnd {
    type ValidationError: error::Error;


    fn state(&self) -> State {
        self.state.clone()
    }
    fn client_id(&self) -> String;
    fn counterparty(&self) -> Box<dyn CounterpartyI<ValidationError = super::error::Error>>;
    fn version(&self) -> String;
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}

pub struct Counterparty {
    client_id: ClientId,
    connection_id: ConnectionId,
    prefix: CommitmentPrefix,
}

impl Counterparty {
    pub fn new(client_id: ClientId, connection_id: ConnectionId, prefix: CommitmentPrefix) -> Self {
        Counterparty {
            client_id,
            connection_id,
            prefix,
        }
    }
}
