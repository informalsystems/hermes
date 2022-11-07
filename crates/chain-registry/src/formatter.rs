//! Contains traits to format the URL of API endpoints from a `&str` to any type.
//! Contains struct to build a `tendermint_rpc::Url` representing a
//! WebSocket URL from a RPC URL and to parse or build a valid `http::Uri`
//! from an (in)complete GRPC URL.
use crate::error::RegistryError;
use http::uri::Scheme;
use http::Uri;
use std::str::FromStr;

use tendermint_rpc::Url;

/// `UriFormatter` contains the basic expectations to parse a valid URL from a `&str`.
pub trait UriFormatter {
    /// Expected output format of the formatter.
    type OutputFormat;

    /// Attempts to parse the given input as a OutputFormat. If the parsed URL
    /// is not complete, this method attempts to fill in the necessary missing
    /// pieces. Returns a RegistryError if this attempt fails.
    ///
    /// # Arguments
    ///
    /// * `url` - A string slice that holds the url which should be formatted
    fn parse_or_build_address(url: &str) -> Result<Self::OutputFormat, RegistryError>;
}

/// `SimpleWebSocketFormatter` contains methods to parse a valid WebSocket URL from an RPC URL.
pub struct SimpleWebSocketFormatter;

/// `SimpleGrpcFormatter` contains methods to parse or build a valid `http::Uri` from an (in)complete GRPC URL.
pub struct SimpleGrpcFormatter;

impl UriFormatter for SimpleWebSocketFormatter {
    type OutputFormat = Url;

    /// Format a WebSocket URL from an RPC URL and return a `tendermint_rpc::Url`.
    fn parse_or_build_address(rpc_address: &str) -> Result<Self::OutputFormat, RegistryError> {
        let uri = rpc_address
            .parse::<Uri>()
            .map_err(|e| RegistryError::uri_parse_error(rpc_address.to_string(), e))?;

        let uri_scheme = if uri.scheme().unwrap_or(&Scheme::HTTP) == &Scheme::HTTPS {
            "wss"
        } else {
            "ws"
        };

        let uri_authority = uri
            .authority()
            .ok_or_else(|| RegistryError::rpc_url_without_authority(rpc_address.to_string()))?
            .clone();

        let uri_websocket = Uri::builder()
            .scheme(uri_scheme)
            .authority(uri_authority)
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

/// Builds a valid `http::Uri` from a gRPC address.
impl UriFormatter for SimpleGrpcFormatter {
    type OutputFormat = Uri;

    fn parse_or_build_address(input: &str) -> Result<Self::OutputFormat, RegistryError> {
        // Remove the last character if it is a '/'
        let input = input.trim_end_matches('/');

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
        // expected is None if the formatter should return an error
        expected: Option<T>,
    }

    impl<T: PartialEq + Debug> FormatterTest<T> {
        fn run<ConcreteFormatter: UriFormatter<OutputFormat = T>>(&self) {
            let output = ConcreteFormatter::parse_or_build_address(self.input);

            match &self.expected {
                Some(expected) => assert_eq!(&output.unwrap(), expected),
                None => assert!(output.is_err()),
            }
        }
    }

    // FormatterTest{input = "", expected = RegistryError::grpc_endpoint_parse_error("".to_string(), http::uri::InvalidUri{..})},
    #[test]
    // Verifies that the SimpleGrpcFormatter can parse a valid gRPC address.
    fn valid_grpc_formatter() {
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
            FormatterTest {
                input: "test",
                expected: Some(Uri::from_str("https://test/").unwrap()), // Not sure about this test case
            },
        ];

        for test in valid_uri {
            test.run::<SimpleGrpcFormatter>();
        }
    }

    #[test]
    fn invalid_grpc_formatter() {
        let valid_uri: &[FormatterTest<Uri>] = &[FormatterTest {
            input: "",
            expected: None,
        }];

        for test in valid_uri {
            test.run::<SimpleGrpcFormatter>();
        }
    }

    #[tokio::test]
    #[ignore]
    async fn all_chain_registry_grpc_address() -> Result<(), RegistryError> {
        use crate::chain::ChainData;
        use crate::constants::ALL_CHAINS;
        use crate::fetchable::Fetchable;

        let mut handles = Vec::with_capacity(ALL_CHAINS.len());

        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(ChainData::fetch(chain.to_string(), None)));
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
        use crate::constants::ALL_CHAINS;
        use crate::fetchable::Fetchable;

        let mut handles = Vec::with_capacity(ALL_CHAINS.len());

        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(ChainData::fetch(chain.to_string(), None)));
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
