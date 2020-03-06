use tendermint::abci;
use tendermint::rpc::{self, endpoint::abci_query::AbciQuery};

use relayer_modules::Height;

use crate::chain::Chain;

mod client_consensus_state;
pub use client_consensus_state::*;

pub trait IbcResponse: Sized {}

pub trait IbcQuery {
    type Response: IbcResponse;

    fn path(&self) -> abci::Path;
    fn height(&self) -> Height;
    fn prove(&self) -> bool;
    fn data(&self) -> Vec<u8>;
}

pub async fn ibc_query<C, Q>(chain: &C, query: Q) -> Result<AbciQuery, rpc::Error>
where
    C: Chain,
    Q: IbcQuery,
{
    let abci_response = chain
        .rpc_client()
        .abci_query(
            Some(query.path()),
            query.data(),
            Some(query.height().into()),
            query.prove(),
        )
        .await?;

    if !abci_response.code.is_ok() {
        todo!() // fail with response log
    }

    // Data from trusted node or subspace query doesn't need verification
    if !is_query_store_with_proof(&query.path()) {
        return Ok(abci_response);
    }

    // TODO: Verify proof and return response
    Ok(abci_response)
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &abci::Path) -> bool {
    todo!()
}
