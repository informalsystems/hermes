use serde_derive::{Deserialize, Serialize};
use std::str::FromStr;

use super::error::ValidationError;
use super::validate::validate_client_identifier;

pub type ClientId = IbcId;

pub type PortId = IbcId;

pub type ChannelId = IbcId;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct IbcId(String);

impl IbcId {
    /// Get this identifier as a borrowed `&str`
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Get this identifier as a borrowed byte slice
    pub fn as_bytes(&self) -> &[u8] {
        &self.0.as_bytes()
    }
}

/// This implementation provides a `to_string` method.
impl std::fmt::Display for IbcId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for IbcId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        validate_client_identifier(s).map(|_| Self(s.to_string()))
    }
}
