use std::marker::PhantomData;
use tendermint::rpc::endpoint::abci_query::AbciQuery;

use tendermint::abci;

use relayer_modules::ics02_client::state::ConsensusState;
use relayer_modules::ics23_commitment::{CommitmentPath, CommitmentProof};
use relayer_modules::ics24_host::client::ClientId;
use relayer_modules::path::{ConsensusStatePath, Path};
use relayer_modules::Height;

use super::{ibc_query, IbcQuery, IbcResponse};
use crate::chain::Chain;
use crate::error;

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
        abci_proof: Option<abci::Proof>,
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
        match (response.value, response.proof) {
            (Some(value), Some(proof)) => {
                let consensus_state = amino_unmarshal_binary_length_prefixed(&value)?;

                Ok(ConsensusStateResponse::new(
                    query.client_id,
                    consensus_state,
                    Some(proof),
                    response.height.into(),
                ))
            }
            (Some(value), _) => {
                let consensus_state = amino_unmarshal_binary_length_prefixed(&value)?;

                Ok(ConsensusStateResponse::new(
                    query.client_id,
                    consensus_state,
                    None,
                    response.height.into(),
                ))
            }
            _ => todo!(),
        }
    }
}

pub async fn query_client_consensus_state<C>(
    chain: &C,
    chain_height: Height,
    client_id: ClientId,
    consensus_height: Height,
    prove: bool,
) -> Result<ConsensusStateResponse<C::ConsensusState>, error::Error>
where
    C: Chain,
{
    let query = QueryClientConsensusState::new(chain_height, client_id, consensus_height, prove);
    println!("XXX Query: {:?}", query.consensus_state_path.to_string());

    ibc_query(chain, query).await
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}
