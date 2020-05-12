use super::exported::*;
use super::error;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ConnectionId, ClientId};


pub struct ConnectionEnd {
    state: State,
    client_id: String,
    counterparty: Counterparty,
    version: String,
}

impl ConnectionEnd{
    pub fn new(
        state: ConnectionState,
        client_id: String,
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

pub struct Counterparty {
    client_id: String,
    connection_id: String,
    prefix: CommitmentPrefix,
}

impl Counterparty {
    pub fn new(
        client_id: String,
        connection_id: String,
        prefix: CommitmentPrefix,
    ) -> Self {
        Counterparty {
            client_id,
            connection_id,
            prefix,
        }
    }
}