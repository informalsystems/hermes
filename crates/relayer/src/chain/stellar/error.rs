use thiserror::Error;

/// Errors produced by the Stellar chain endpoint.
#[derive(Debug, Error)]
pub enum Error {
    /// JSON-RPC call to stellar-rpc failed.
    #[error("Stellar RPC client error: {0}")]
    RpcClient(String),

    /// Configuration field is invalid or missing.
    #[error("Stellar config error: {0}")]
    Config(String),

    /// Keyring operation failed (key not found, derivation error, etc.).
    #[error("Stellar keyring error: {0}")]
    Keyring(String),

    /// Transaction signing failed.
    #[error("Stellar signer error: {0}")]
    Signer(String),

    /// XDR encode or decode failed.
    #[error("Stellar XDR error: {0}")]
    XdrDecode(String),

    /// Transaction submission or polling failed.
    #[error("Stellar transaction error: {0}")]
    Transaction(String),

    /// Chain query returned an unexpected result.
    #[error("Stellar query error: {0}")]
    Query(String),

    /// IBC message encoding or decoding failed.
    #[error("Stellar IBC error: {0}")]
    Ibc(String),

    /// Contract event could not be parsed into an IBC event.
    #[error("Stellar event parse error: {0}")]
    EventParse(String),

    /// Generic catch-all for unexpected errors.
    #[error("Stellar error: {0}")]
    Generic(String),
}

impl Error {
    pub fn rpc_client(msg: impl Into<String>) -> Self {
        Self::RpcClient(msg.into())
    }

    pub fn config(msg: impl Into<String>) -> Self {
        Self::Config(msg.into())
    }

    pub fn query(msg: impl Into<String>) -> Self {
        Self::Query(msg.into())
    }

    pub fn xdr_decode(msg: impl Into<String>) -> Self {
        Self::XdrDecode(msg.into())
    }

    pub fn transaction(msg: impl Into<String>) -> Self {
        Self::Transaction(msg.into())
    }

    pub fn event_parse(msg: impl Into<String>) -> Self {
        Self::EventParse(msg.into())
    }

    pub fn generic(msg: impl Into<String>) -> Self {
        Self::Generic(msg.into())
    }
}
