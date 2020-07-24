use crate::chain::Chain;
use relayer_modules::error;
use relayer_modules::try_from_raw::TryFromRaw;
use tendermint::abci::Path as TendermintPath;
use tendermint::block;

pub mod client;

/// Query the ABCI application for information
pub struct Request {
    /// Path to the data
    pub path: Option<TendermintPath>,

    /// Data to query
    pub data: String,

    /// Block height
    pub height: u64,

    /// Include proof in response
    pub prove: bool,
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proof expects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &TendermintPath) -> bool {
    false
}

/// Perform a generic `abci_query` on the given `chain`, and return the corresponding deserialized response data.
pub async fn query<C, T, O>(chain: &C, request: O) -> Result<T, error::Error>
where
    C: Chain,         // Chain configuration
    T: TryFromRaw,    // Internal Struct type (expected response)
    O: Into<Request>, // Query Command configuration (opts)
{
    // RPC Request
    let request: Request = request.into();
    let path = request.path.clone().unwrap(); // for the is_query_store_with_proof function

    // Use the Tendermint-rs RPC client to do the query.
    // Todo: generalize further for other type of chains (#157).
    let response = chain
        .rpc_client()
        .abci_query(
            request.path,
            request.data.to_string().into_bytes(),
            match request.height {
                0 => None,
                _ => Some(block::Height::from(request.height)),
            },
            request.prove,
        )
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(error::Kind::Rpc.context(response.log.to_string()).into());
    }
    if response.value.is_empty() {
        // Fail due to empty response value (nothing to decode).
        return Err(error::Kind::EmptyResponseValue.into());
    }

    // Verify response proof.
    // Data that is not from trusted node or subspace query needs verification.
    if is_query_store_with_proof(&path) {
        todo!() // TODO: Verify proof
    }

    // Deserialize response data.
    T::deserialize(response.value)
}
