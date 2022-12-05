use crate::chain::requests::CrossChainQueryRequest;
use crate::error::Error;
use hex;
use ibc_relayer_types::applications::ics31_icq::{
    error::Error as CrossChainQueryError, response::CrossChainQueryResponse,
};
use tendermint_rpc::{Client, HttpClient};

pub async fn cross_chain_query_via_rpc(
    client: &HttpClient,
    cross_chain_query_request: CrossChainQueryRequest,
) -> Result<CrossChainQueryResponse, Error> {
    let hex_decoded_request = hex::decode(cross_chain_query_request.request)
        .map_err(|_| Error::ics31(CrossChainQueryError::parse()))?;

    let response = client
        .abci_query(
            Some(cross_chain_query_request.query_type),
            hex_decoded_request,
            Some(cross_chain_query_request.height),
            true,
        )
        .await
        .map_err(|_| Error::ics31(CrossChainQueryError::query()))?;

    if !response.code.is_ok() {
        return Err(Error::ics31(CrossChainQueryError::query()));
    }

    if response.proof.is_none() {
        return Err(Error::ics31(CrossChainQueryError::proof()));
    }

    Ok(CrossChainQueryResponse::new(
        cross_chain_query_request.chain_id.to_string(),
        cross_chain_query_request.query_id,
        response.value,
        response
            .height
            .value()
            .try_into()
            .map_err(|_| Error::ics31(CrossChainQueryError::parse()))?,
        response.proof.unwrap(),
    ))
}
