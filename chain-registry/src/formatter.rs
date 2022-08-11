use crate::error::RegistryError;
use http::uri::Scheme;
use http::Uri;
use std::str::FromStr;

use tendermint_rpc::Url;

pub trait UriFormatter {
    /// Attempts to parse the given input as a OutputFormat. If the parsed URI
    /// is not complete, this method attempts to fill in the necessary missing
    /// pieces or return a RegistryError.
    type OutputFormat;
    fn parse_or_build_address(grpc: &str) -> Result<Self::OutputFormat, RegistryError>;
}

pub struct SimpleWebSocketFormatter;
pub struct SimpleGrpcFormatter;

/// Format a websocket address from a rpc address and return a tendermint_rpc::Url.
impl UriFormatter for SimpleWebSocketFormatter {
    type OutputFormat = Url;
    fn parse_or_build_address(rpc_address: &str) -> Result<Self::OutputFormat, RegistryError> {
        let uri = rpc_address
            .parse::<Uri>()
            .map_err(|e| RegistryError::uri_parse_error(rpc_address.to_string(), e))?;

        let uri_websocket = Uri::builder()
            .scheme(if uri.scheme().unwrap_or(&Scheme::HTTP) == &Scheme::HTTPS {
                "wss"
            } else {
                "ws"
            })
            .authority(
                uri.authority()
                    .ok_or_else(|| {
                        RegistryError::rpc_url_without_authority(rpc_address.to_string())
                    })?
                    .clone(),
            )
            .path_and_query("/websocket")
            .build();

        match uri_websocket {
            Ok(uri_websocket) => Ok(Url::from_str(uri_websocket.to_string().as_str()).map_err(
                |e| RegistryError::tendermint_url_parse_error(rpc_address.to_string(), e),
            )?),
            Err(e) => Err(RegistryError::unable_to_build_websocket_endpoint(
                rpc_address.to_string(),
                e,
            )),
        }
    }
}

/// Builds a valid http::Uri from a gRPC address.
impl UriFormatter for SimpleGrpcFormatter {
    type OutputFormat = Uri;
    fn parse_or_build_address(input: &str) -> Result<Self::OutputFormat, RegistryError> {
        // Remove the last character if it is a '/'
        let input = match input.ends_with('/') {
            false => input,
            true => {
                let mut chars = input.chars();
                chars.next_back();
                chars.as_str()
            }
        };

        let uri = input
            .parse::<Uri>()
            .map_err(|e| RegistryError::uri_parse_error(input.to_string(), e))?;

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

#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp::PartialEq;
    use std::fmt::Debug;

    struct FormatterTest<T> {
        input: &'static str,
        expected: Option<T>,
    }
    impl<T: PartialEq + Debug> FormatterTest<T> {
        fn run<ConcreteFormatter: UriFormatter<OutputFormat = T>>(&self) {
            let output = ConcreteFormatter::parse_or_build_address(self.input);
            match &self.expected {
                Some(expected) => {
                    assert_eq!(&output.unwrap(), expected);
                }
                None => {
                    assert!(!output.is_ok());
                }
            }
        }
    }
    // FormatterTest{input = "", expected = RegistryError::grpc_endpoint_parse_error("".to_string(), http::uri::InvalidUri{..})},
    #[test]
    // Verifies that the SimpleGrpcFormatter can parse a valid gRPC address.
    fn valid_grpc_formatter_test() {
        let valid_uri: &[FormatterTest<Uri>] = &[
            FormatterTest {
                input: "test.com",
                expected: Some(Uri::from_str("https://test.com/").unwrap()),
            },
            FormatterTest {
                input: "test.com:9090",
                expected: Some(Uri::from_str("https://test.com:9090/").unwrap()),
            },
            FormatterTest {
                input: "tcp://test.com",
                expected: Some(Uri::from_str("tcp://test.com/").unwrap()),
            },
            FormatterTest {
                input: "tcp://test.com:9090",
                expected: Some(Uri::from_str("tcp://test.com:9090/").unwrap()),
            },
            FormatterTest {
                input: "https://test.com",
                expected: Some(Uri::from_str("https://test.com/").unwrap()),
            },
            FormatterTest {
                input: "https://test.com:9090",
                expected: Some(Uri::from_str("https://test.com:9090").unwrap()),
            },
            FormatterTest {
                input: "https://test.com:9090",
                expected: Some(Uri::from_str("https://test.com:9090").unwrap()),
            },
            FormatterTest {
                input: "test.com/",
                expected: Some(Uri::from_str("https://test.com/").unwrap()),
            },
        ];

        for test in valid_uri {
            test.run::<SimpleGrpcFormatter>();
        }
    }

    #[tokio::test]
    #[ignore]
    async fn all_chain_registry_grpc_address() -> Result<(), RegistryError> {
        use crate::chain::ChainData;
        use crate::utils::Fetchable;
        use crate::utils::ALL_CHAINS;
        let mut handles = Vec::with_capacity(ALL_CHAINS.len());
        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(ChainData::fetch(chain.to_string())));
        }

        for handle in handles {
            let chain_data = handle.await.unwrap()?;
            for grpc in chain_data.apis.grpc.iter() {
                SimpleGrpcFormatter::parse_or_build_address(grpc.address.as_str())?;
            }
        }
        Ok(())
    }

    #[tokio::test]
    #[ignore]
    async fn all_chain_registry_rpc_address() -> Result<(), RegistryError> {
        use crate::chain::ChainData;
        use crate::utils::Fetchable;
        use crate::utils::ALL_CHAINS;
        let mut handles = Vec::with_capacity(ALL_CHAINS.len());
        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(ChainData::fetch(chain.to_string())));
        }

        for handle in handles {
            let chain_data = handle.await.unwrap()?;
            for rpc in chain_data.apis.rpc.iter() {
                SimpleWebSocketFormatter::parse_or_build_address(rpc.address.as_str())?;
            }
        }
        Ok(())
    }
}
