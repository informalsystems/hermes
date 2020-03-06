use std::marker::PhantomData;

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
    pub height: Height,
    pub consensus_state_path: ConsensusStatePath,
    marker: PhantomData<CS>,
}

impl<CS> QueryClientConsensusState<CS> {
    pub fn new(height: Height, client_id: ClientId) -> Self {
        Self {
            height,
            consensus_state_path: ConsensusStatePath { client_id, height },
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
        self.height
    }

    fn prove(&self) -> bool {
        true
    }

    fn data(&self) -> Vec<u8> {
        self.consensus_state_path.to_key().into()
    }
}

pub struct ConsensusStateResponse<CS> {
    pub consensus_state: CS,
    pub proof: CommitmentProof,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl<CS> ConsensusStateResponse<CS> {
    pub fn new(
        client_id: ClientId,
        consensus_state: CS,
        abci_proof: abci::Proof,
        proof_height: Height,
    ) -> Self {
        let proof = CommitmentProof::from_bytes(abci_proof.as_ref());
        let proof_path =
            CommitmentPath::from_path(ConsensusStatePath::new(client_id, proof_height));

        ConsensusStateResponse {
            consensus_state,
            proof,
            proof_path,
            proof_height,
        }
    }
}

impl<CS> IbcResponse for ConsensusStateResponse<CS>
where
    CS: ConsensusState,
{
    // fn from_bytes(_bytes: &[u8]) -> Result<Self, rpc::Error> {
    //     todo!()
    // }
}

pub async fn query_client_consensus_state<C>(
    chain: &C,
    client_id: ClientId,
    height: Height,
) -> Result<ConsensusStateResponse<C::ConsensusState>, error::Error>
where
    C: Chain,
{
    let query = QueryClientConsensusState::<C::ConsensusState>::new(height, client_id.clone());

    let response = ibc_query(chain, query)
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    // FIXME: Handle case where there is no value
    let consensus_state = amino_unmarshal_binary_length_prefixed(&response.value.unwrap())?;

    Ok(ConsensusStateResponse::new(
        client_id,
        consensus_state,
        response.proof.unwrap(), // FIXME: Handle case where there is no proof
        response.height.into(),
    ))
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}
