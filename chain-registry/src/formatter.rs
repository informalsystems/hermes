use crate::error::RegistryError;
use http::Uri;
use std::str::FromStr;

pub trait UriFormatter {
    /// Attempts to parse the given input as a OutputFormat. If the parsed URI
    /// is not complete, this method attempts to fill in the necessary missing
    /// pieces or return a RegistryError.
    type OutputFormat;
    fn parse_or_build_address(grpc: &str) -> Result<Self::OutputFormat, RegistryError>;
}

pub struct WebSocketFormatter;
pub struct GRPCFormatter;

impl UriFormatter for WebSocketFormatter {
    type OutputFormat = tendermint_rpc::Url;
    fn parse_or_build_address(rpc_endpoint: &str) -> Result<Self::OutputFormat, RegistryError> {
        let uri = rpc_endpoint
            .parse::<Uri>()
            .map_err(|e| RegistryError::uri_parse_error(rpc_endpoint.to_string(), e))?;

        let uri = Uri::builder()
            .scheme("wss")
            .authority(
                uri.authority()
                    .ok_or_else(|| {
                        RegistryError::rpc_url_without_authority(rpc_endpoint.to_string())
                    })?
                    .clone(),
            )
            .path_and_query("/websocket")
            .build();

        match uri {
            Ok(uri) => Ok(
                tendermint_rpc::Url::from_str(uri.to_string().as_str()).map_err(|e| {
                    RegistryError::tendermint_url_parse_error(rpc_endpoint.to_string(), e)
                })?,
            ),
            Err(e) => Err(RegistryError::unable_to_build_websocket_endpoint(
                rpc_endpoint.to_string(),
                e,
            )),
        }
    }
}

impl UriFormatter for GRPCFormatter {
    type OutputFormat = Uri;
    fn parse_or_build_address(input: &str) -> Result<Self::OutputFormat, RegistryError> {
        let uri = input
            .parse::<Uri>()
            .map_err(|e| RegistryError::uri_parse_error(input.to_string(), e))?;
        /*
        TODO : check if a valid grpc must provide a port
        if uri.port().is_none() {
            return Err(RegistryError::grpc_without_port(input.to_string()));
        }
        */

        if uri.scheme().is_none() {
            let builder = Uri::builder();
            return builder
                .scheme("https")
                .authority(input)
                .path_and_query("/")
                .build()
                .map_err(|e| RegistryError::grpc_endpoint_parse_error(input.to_string(), e));
        }

        Ok(uri)
    }
}
