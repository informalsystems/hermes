use std::marker::PhantomData;
use tendermint_rpc::endpoint::abci_query::AbciQuery;

use tendermint::abci;

use crate::ics23_commitment::{CommitmentPath, CommitmentProof};

use crate::error;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics24_host::identifier::ClientId;
use crate::path::{ClientStatePath, ConsensusStatePath, Path};
use crate::query::{IbcQuery, IbcResponse};
use crate::Height;

pub struct QueryClientFullState<CLS> {
    pub chain_height: Height,
    pub client_id: ClientId,
    pub client_state_path: ClientStatePath,
    pub prove: bool,
    marker: PhantomData<CLS>,
}

impl<CLS> QueryClientFullState<CLS> {
    pub fn new(chain_height: Height, client_id: ClientId, prove: bool) -> Self {
        Self {
            chain_height,
            client_id: client_id.clone(),
            client_state_path: ClientStatePath::new(client_id),
            prove,
            marker: PhantomData,
        }
    }
}

impl<CLS> IbcQuery for QueryClientFullState<CLS>
where
    CLS: ClientState,
{
    type Response = ClientFullStateResponse<CLS>;

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
        self.client_state_path.to_key().into()
    }
}

pub struct ClientFullStateResponse<CLS> {
    pub client_state: CLS,
    pub proof: Option<CommitmentProof>,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl<CLS> ClientFullStateResponse<CLS> {
    pub fn new(
        client_id: ClientId,
        client_state: CLS,
        abci_proof: Option<CommitmentProof>,
        proof_height: Height,
    ) -> Self {
        let proof_path = CommitmentPath::from_path(ClientStatePath::new(client_id));

        ClientFullStateResponse {
            client_state,
            proof: abci_proof,
            proof_path,
            proof_height,
        }
    }
}

impl<CLS> IbcResponse<QueryClientFullState<CLS>> for ClientFullStateResponse<CLS>
where
    CLS: ClientState,
{
    fn from_abci_response(
        query: QueryClientFullState<CLS>,
        response: AbciQuery,
    ) -> Result<Self, error::Error> {
        Ok(ClientFullStateResponse::new(
            query.client_id,
            amino_unmarshal_binary_length_prefixed(&response.value)?,
            response.proof,
            response.height.into(),
        ))
    }
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}

pub struct QueryClientConsensusState<CS> {
    pub chain_height: Height,
    pub client_id: ClientId,
    pub consensus_height: Height,
    pub consensus_state_path: ConsensusStatePath,
    pub prove: bool,
    marker: PhantomData<CS>,
}

impl<CS> QueryClientConsensusState<CS> {
    pub fn new(
        chain_height: Height,
        client_id: ClientId,
        consensus_height: Height,
        prove: bool,
    ) -> Self {
        Self {
            chain_height,
            client_id: client_id.clone(),
            consensus_height,
            consensus_state_path: ConsensusStatePath::new(client_id, consensus_height),
            prove,
            marker: PhantomData,
        }
    }
}

impl<CS> IbcQuery for QueryClientConsensusState<CS>
where
    CS: ConsensusState,
{
    type Response = ConsensusStateResponse<CS>;

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
        self.consensus_state_path.to_key().into()
    }
}

pub struct ConsensusStateResponse<CS> {
    pub consensus_state: CS,
    pub proof: Option<CommitmentProof>,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl<CS> ConsensusStateResponse<CS> {
    pub fn new(
        client_id: ClientId,
        consensus_state: CS,
        abci_proof: Option<CommitmentProof>,
        proof_height: Height,
    ) -> Self {
        let proof_path =
            CommitmentPath::from_path(ConsensusStatePath::new(client_id, proof_height));

        ConsensusStateResponse {
            consensus_state,
            proof: abci_proof,
            proof_path,
            proof_height,
        }
    }
}

impl<CS> IbcResponse<QueryClientConsensusState<CS>> for ConsensusStateResponse<CS>
where
    CS: ConsensusState,
{
    fn from_abci_response(
        query: QueryClientConsensusState<CS>,
        response: AbciQuery,
    ) -> Result<Self, error::Error> {
        Ok(ConsensusStateResponse::new(
            query.client_id,
            amino_unmarshal_binary_length_prefixed(&response.value)?,
            response.proof,
            response.height.into(),
        ))
    }
}
