use crate::chain::Chain;
use bytes::Bytes;
use prost::Message;
use relayer_modules::error;
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::abci::Path;
use tendermint::block;

pub mod client;

// This struct was copied form tenderint-rs rpc/source/endpoint/abci_query.rs and made public.
// Todo: Work on removing it by consolidating the Request part of every query function - maybe with a helper function.
/// Query the ABCI application for information
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Request {
    /// Path to the data
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<Path>,

    /// Data to query
    //#[serde(with = "serializers::bytes::hexstring")]
    pub data: Vec<u8>,

    /// Block height
    #[serde(skip_serializing_if = "Option::is_none")]
    pub height: Option<block::Height>,

    /// Include proof in response
    pub prove: bool,
}

/// Whether or not this path requires proof verification.
///
/// is_query_store_with_proofxpects a format like /<queryType>/<storeName>/<subpath>,
/// where queryType must be "store" and subpath must be "key" to require a proof.
fn is_query_store_with_proof(_path: &Path) -> bool {
    false
}

/// Perform a generic `abci_query` on the given `chain`, and return the corresponding deserialized response data.
pub async fn query<C, R, T>(chain: &C, request: Request) -> Result<T, error::Error>
where
    C: Chain,
    R: Message + Default,
    T: TryFrom<R>,
{
    // RPC Request

    let path = request.path.clone().unwrap();
    // Use the Tendermint-rs RPC client to do the query
    let abci_response = chain
        .rpc_client()
        .abci_query(request.path, request.data, request.height, request.prove)
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
