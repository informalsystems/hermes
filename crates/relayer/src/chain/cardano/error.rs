//! Error types for Cardano chain implementation

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Gateway client error: {0}")]
    GatewayClient(String),

    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Keyring error: {0}")]
    Keyring(String),

    #[error("Signer error: {0}")]
    Signer(String),

    #[error("CBOR decode error: {0}")]
    CborDecode(String),

    #[error("Transaction error: {0}")]
    Transaction(String),

    #[error("Query error: {0}")]
    Query(String),

    #[error("IBC error: {0}")]
    Ibc(String),

    #[error("Event attribute error: {0}")]
    EventAttribute(String),

    #[error("Generic error: {0}")]
    Generic(String),
}

// Conversion from other error types
impl From<tonic::Status> for Error {
    fn from(err: tonic::Status) -> Self {
        Error::GatewayClient(err.message().to_string())
    }
}

impl From<tonic::transport::Error> for Error {
    fn from(err: tonic::transport::Error) -> Self {
        Error::GatewayClient(err.to_string())
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::Generic(err.to_string())
    }
}

impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Self {
        Error::Generic(err.to_string())
    }
}
