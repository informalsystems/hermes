use tendermint::abci;

use crate::chain::Chain;
use relayer_modules::error;
use relayer_modules::query::IbcQuery;
// use tracing::debug;

pub mod channel;
pub mod client;
pub mod connection;

/// Perform an IBC `query` on the given `chain`, and return the corresponding IBC response.
pub async fn ibc_query<C, Q>(chain: &C, query: Q) -> Result<Q::Response, error::Error>
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
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    if !abci_response.code.is_ok() {
        todo!() // TODO: Fail with response log
    }

    // Data that is not from trusted node or subspace query needs verification
    if is_query_store_with_proof(&query.path()) {
        todo!() // TODO: Verify proof
    }

    // debug!("done with 'query connection end' command: {:?}", abci_response);

    query.build_response(abci_response)
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &abci::Path) -> bool {
    false
}
