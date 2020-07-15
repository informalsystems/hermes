use tendermint::abci;

use crate::chain::Chain;
use relayer_modules::error;
use relayer_modules::query::IbcQuery;

pub mod client;

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
        // Fail with response log
        return Err(error::Kind::Rpc
            .context(abci_response.log.to_string())
            .into());
    }

    // Data that is not from trusted node or subspace query needs verification
    if is_query_store_with_proof(&query.path()) {
        todo!() // TODO: Verify proof
    }

    query.build_response(abci_response)
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &abci::Path) -> bool {
    false
}
