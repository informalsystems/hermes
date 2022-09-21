use serde::ser::{Serialize, SerializeMap, Serializer};
use thiserror::Error;

use ibc::core::ics24_host::{error::ValidationErrorDetail, identifier::ChainId};

#[derive(Error, Debug)]
pub enum RestApiError {
    #[error("failed to send a request through crossbeam channel: {0}")]
    ChannelSend(String),

    #[error("failed to receive a reply from crossbeam channel: {0}")]
    ChannelRecv(String),

    #[error("failed while serializing reply into json value: {0}")]
    Serialization(String),

    #[error("could not find configuration for chain: {0}")]
    ChainConfigNotFound(ChainId),

    #[error("failed to parse the string {0} into a valid chain identifier: {1}")]
    InvalidChainId(String, ValidationErrorDetail),

    #[error("failed while parsing the request body into a chain configuration: {0}")]
    InvalidChainConfig(String),

    #[error("not implemented")]
    Unimplemented,
}

impl RestApiError {
    pub fn name(&self) -> &'static str {
        match self {
            RestApiError::ChannelSend(_) => "ChannelSend",
            RestApiError::ChannelRecv(_) => "ChannelRecv",
            RestApiError::Serialization(_) => "Serialization",
            RestApiError::ChainConfigNotFound(_) => "ChainConfigNotFound",
            RestApiError::InvalidChainId(_, _) => "InvalidChainId",
            RestApiError::InvalidChainConfig(_) => "InvalidChainConfig",
            RestApiError::Unimplemented => "Unimplemented",
        }
    }
}

impl Serialize for RestApiError {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(3))?;
        map.serialize_entry("name", self.name())?;
        map.serialize_entry("msg", &self.to_string())?;
        map.end()
    }
}
