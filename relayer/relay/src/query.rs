use crate::chain::Chain;
use bytes::Bytes;
use prost::Message;
use relayer_modules::error;
use std::convert::TryFrom;
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
    pub height: Option<u64>,

    /// Include proof in response
    pub prove: bool,
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &TendermintPath) -> bool {
    false
}

/// Perform a generic `abci_query` on the given `chain`, and return the corresponding deserialized response data.
pub async fn query<C, R, T>(chain: &C, request: Request) -> Result<T, error::Error>
where
    C: Chain,             // Chain configuration
    R: Message + Default, // Raw Struct type
    T: TryFrom<R>,        // Internal Struct type
    O: Into<Request>,     // Query Command configuration (opts)
{
    // RPC Request

    let request: Request = request.into();
    let path = request.path.clone().unwrap(); // for the is_query_store_with_proof function

    // Use the Tendermint-rs RPC client to do the query
    let abci_response = chain
        .rpc_client()
        .abci_query(
            request.path,
            request.data.to_string().into_bytes(),
            request.height.map(|h| block::Height::from(h)),
            request.prove,
        )
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    if !abci_response.code.is_ok() {
        // Fail with response log
        return Err(error::Kind::Rpc
            .context(abci_response.log.to_string())
            .into());
    }
    if abci_response.value.is_empty() {
        // Fail due to empty response value (nothing to decode).
        return Err(error::Kind::EmptyResponseValue.into());
    }

    // Verify response proof

    // Data that is not from trusted node or subspace query needs verification
    if is_query_store_with_proof(&path) {
        todo!() // TODO: Verify proof
    }

    // Deserialize response data

    // Poor man's serde(from='P') - this can be simplified if we use a serde-compatible protobuf implementation
    let proto_type = R::decode(Bytes::from(abci_response.value))
        .map_err(|e| error::Kind::ResponseParsing.context(e))?;
    T::try_from(proto_type).map_err(|_e| error::Kind::ResponseParsing.into()) // Todo: Add context to error
}
