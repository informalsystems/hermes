use tendermint::abci;
use tendermint::rpc::endpoint::abci_query::AbciQuery;

use relayer_modules::Height;

use crate::chain::Chain;
use crate::error;

pub mod client_consensus_state;

/// The type of IBC response sent back for a given IBC `Query`.
pub trait IbcResponse<Query>: Sized {
    /// The type of the raw response returned by the interface used to query the chain
    ///
    /// TODO: Uncomment once we abstract over the IBC client
    // type RawType;

    /// Build a response of this type from the initial `query` and the IBC `response`.
    ///
    /// TODO: Replace `AbciQuery` with `Self::RawType`
    fn from_abci_response(query: Query, response: AbciQuery) -> Result<Self, error::Error>;
}

/// Defines an IBC query
pub trait IbcQuery: Sized {
    type Response: IbcResponse<Self>;

    fn path(&self) -> abci::Path;
    fn height(&self) -> Height;
    fn prove(&self) -> bool;
    fn data(&self) -> Vec<u8>;

    /// Build a `Response` from a raw `AbciQuery` response
    ///
    /// TODO: Replace `AbciQuery` with `<Self::Response as IbcResponse<Self>>::RawType`
    fn build_response(self, response: AbciQuery) -> Result<Self::Response, error::Error> {
        Self::Response::from_abci_response(self, response)
    }
}

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

    query.build_response(abci_response)
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &abci::Path) -> bool {
    todo!()
}
