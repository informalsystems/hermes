use tendermint::rpc::endpoint::abci_query::AbciQuery;

use tendermint::abci;

use crate::ics23_commitment::{CommitmentPath, CommitmentProof};
use crate::ics24_host::identifier::ConnectionId;

use crate::error;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::path::{ConnectionPath, Path};
use crate::query::{IbcQuery, IbcResponse};
use crate::Height;

pub struct QueryConnection {
    pub chain_height: Height,
    pub connection_id: ConnectionId,
    pub connection_path: ConnectionPath,
    pub prove: bool,
}

impl QueryConnection {
    pub fn new(chain_height: Height, connection_id: ConnectionId, prove: bool) -> Self {
        Self {
            chain_height,
            connection_id: connection_id.clone(),
            connection_path: ConnectionPath::new(connection_id),
            prove,
        }
    }
}

impl IbcQuery for QueryConnection {
    type Response = ConnectionResponse;

    fn path(&self) -> abci::Path {
        "/store/ibc/key".parse().unwrap()
    }

    fn height(&self) -> Height {
        self.chain_height
    }

    fn prove(&self) -> bool {
        self.prove
    }

    fn data(&self) -> Vec<u8> {
        self.connection_path.to_key().into()
    }
}

pub struct ConnectionResponse {
    pub connection: IdentifiedConnectionEnd,
    pub proof: Option<CommitmentProof>,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl ConnectionResponse {
    pub fn new(
        connection_id: ConnectionId,
        connection: ConnectionEnd,
        abci_proof: Option<CommitmentProof>,
        proof_height: Height,
    ) -> Self {
        let proof_path = CommitmentPath::from_path(ConnectionPath::new(connection_id.clone()));
        let identified_connection_end = IdentifiedConnectionEnd::new(connection, connection_id);
        ConnectionResponse {
            connection: identified_connection_end,
            proof: abci_proof,
            proof_path,
            proof_height,
        }
    }
}

impl IbcResponse<QueryConnection> for ConnectionResponse {
    fn from_abci_response(
        query: QueryConnection,
        response: AbciQuery,
    ) -> Result<Self, error::Error> {
        let connection = amino_unmarshal_binary_length_prefixed(&response.value)?;

        Ok(ConnectionResponse::new(
            query.connection_id,
            connection,
            response.proof,
            response.height.into(),
        ))
    }
}

#[derive(Debug)]
pub struct IdentifiedConnectionEnd {
    connection_end: ConnectionEnd,
    connection_id: ConnectionId,
}

impl IdentifiedConnectionEnd {
    pub fn new(connection_end: ConnectionEnd, connection_id: ConnectionId) -> Self {
        IdentifiedConnectionEnd {
            connection_end,
            connection_id,
        }
    }
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}
