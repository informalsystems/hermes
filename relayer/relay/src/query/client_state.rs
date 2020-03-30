use std::marker::PhantomData;
use tendermint::rpc::endpoint::abci_query::AbciQuery;

use tendermint::abci;

use relayer_modules::ics02_client::state::ClientState;
use relayer_modules::ics23_commitment::{CommitmentPath, CommitmentProof};
use relayer_modules::ics24_host::client::ClientId;
use relayer_modules::path::{ClientStatePath, Path};
use relayer_modules::Height;

use super::{ibc_query, IbcQuery, IbcResponse};
use crate::chain::Chain;
use crate::error;

pub struct QueryClientLatestState<CLS> {
    pub chain_height: Height,
    pub client_id: ClientId,
    pub client_state_path: ClientStatePath,
    pub prove: bool,
    marker: PhantomData<CLS>,
}

impl<CLS> QueryClientLatestState<CLS> {
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

impl<CLS> IbcQuery for QueryClientLatestState<CLS>
where
    CLS: ClientState,
{
    type Response = ClientStateResponse<CLS>;

    fn path(&self) -> abci::Path {
        "/store/ibc/key".parse().unwrap()
    }

    fn height(&self) -> Height {
        self.chain_height
    }

    fn prove(&self) -> bool {
        true
    }

    fn data(&self) -> Vec<u8> {
        self.client_state_path.to_key().into()
    }
}

pub struct ClientStateResponse<CLS> {
    pub client_state: CLS,
    pub proof: Option<CommitmentProof>,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl<CLS> ClientStateResponse<CLS> {
    pub fn new(
        client_id: ClientId,
        client_state: CLS,
        abci_proof: Option<abci::Proof>,
        proof_height: Height,
    ) -> Self {
        let mut proof: CommitmentProof = CommitmentProof;
        match abci_proof {
            Some(abci_proof) => {
                proof = CommitmentProof::from_bytes(abci_proof.as_ref());
            }
            None => {}
        }
        let proof_path =
            CommitmentPath::from_path(ClientStatePath::new(client_id));

        ClientStateResponse {
            client_state,
            proof: Option::from(proof),
            proof_path,
            proof_height,
        }
    }
}

impl<CLS> IbcResponse<QueryClientLatestState<CLS>> for ClientStateResponse<CLS>
where
    CLS: ClientState,
{
    fn from_abci_response(
        query: QueryClientLatestState<CLS>,
        response: AbciQuery,
    ) -> Result<Self, error::Error> {
        match (response.value, response.proof) {
            (Some(value), Some(proof)) => {
                let consensus_state = amino_unmarshal_binary_length_prefixed(&value)?;

                Ok(ClientStateResponse::new(
                    query.client_id,
                    consensus_state,
                    Some(proof),
                    response.height.into(),
                ))
            }
            _ => todo!(),
        }
    }
}

pub async fn query_client_latest_state<C>(
    chain: &C,
    chain_height: Height,
    client_id: ClientId,
    prove: bool,
) -> Result<ClientStateResponse<C::ClientState>, error::Error>
where
    C: Chain,
{
    let query = QueryClientLatestState::new(chain_height, client_id, prove);
    println!("XXX Query: {:?}", query.client_state_path.to_string());

    ibc_query(chain, query).await
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}
