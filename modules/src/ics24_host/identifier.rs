use serde_derive::{Deserialize, Serialize};
use std::str::FromStr;

use super::error::ValidationError;
use super::validate::*;
use crate::ics24_host::error::ValidationKind;

/// This type is subject to future changes.
/// TODO: ChainId validation is not standardized yet.
/// `is_epoch_format` will most likely be replaced by validate_chain_id()-style function.
/// https://github.com/informalsystems/ibc-rs/pull/304#discussion_r503917283.
/// Also, contrast with tendermint-rs `ChainId` type.
#[derive(Clone, Debug)]
pub struct ChainId(String);

impl ChainId {
    /// Creates a new ChainId() given a chain name and an epoch number. May fail by returning an
    /// error if the epoch is 0.
    /// The returned chainID will have the format: `{chain name}-{epoch number}`.
    /// ```
    /// use ibc::ics24_host::identifier::ChainId;
    /// assert!(ChainId::new("chainA", 0).is_err());
    /// assert!(ChainId::new("chainA", 1).is_ok());
    /// let epoch_number = 10;
    /// let c_res = ChainId::new("chainA", epoch_number);
    /// assert!(c_res.is_ok());
    /// c_res.map(|id| {assert_eq!(ChainId::chain_version(id.to_string()), epoch_number)});
    /// ```
    pub fn new(chain_name: &str, chain_epoch_number: u64) -> Result<Self, ValidationError> {
        ChainId::from_str(format!("{}-{}", chain_name, chain_epoch_number.to_string()).as_str())
    }

    /// is_epoch_format() checks if a chain_id is in the format required for parsing epochs
    /// The chainID must be in the form: `{chainID}-{version}`
    /// ```
    /// use ibc::ics24_host::identifier::ChainId;
    /// assert_eq!(ChainId::is_epoch_format("chainA-0".to_string()), false);
    /// assert_eq!(ChainId::is_epoch_format("chainA".to_string()), false);
    /// assert_eq!(ChainId::is_epoch_format("chainA-1".to_string()), true);
    /// ```
    pub fn is_epoch_format(chain_id: String) -> bool {
        use regex::Regex;
        let re = Regex::new(r"^.+[^-]-{1}[1-9][0-9]*$").unwrap();
        re.is_match(chain_id.as_str())
    }

    // todo: this should probably be named epoch_number.
    pub fn chain_version(chain_id: String) -> u64 {
        if !Self::is_epoch_format(chain_id.clone()) {
            return 0;
        }
        let split: Vec<_> = chain_id.split('-').collect();
        split[1].parse().unwrap_or(0)
    }
}

impl FromStr for ChainId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match Self::is_epoch_format(s.to_string()) {
            true => Ok(Self(s.to_string())),
            false => Err(ValidationKind::chain_id_invalid_format(s.into()).into()),
        }
    }
}

impl std::fmt::Display for ChainId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ClientId(String);

impl ClientId {
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
impl std::fmt::Display for ClientId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ClientId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        validate_client_identifier(s).map(|_| Self(s.to_string()))
    }
}

impl Default for ClientId {
    fn default() -> Self {
        "defaultclientid".to_string().parse().unwrap()
    }
}

/// Equality check against string literal (satisfies &ClientId == &str).
/// ```
/// use std::str::FromStr;
/// use ibc::ics24_host::identifier::ClientId;
/// let client_id = ClientId::from_str("clientidtwo");
/// assert!(client_id.is_ok());
/// client_id.map(|id| {assert_eq!(&id, "clientidtwo")});
/// ```
impl PartialEq<str> for ClientId {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConnectionId(String);

impl ConnectionId {
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
impl std::fmt::Display for ConnectionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ConnectionId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        validate_connection_identifier(s).map(|_| Self(s.to_string()))
    }
}

impl Default for ConnectionId {
    fn default() -> Self {
        "defaultconnectionid".to_string().parse().unwrap()
    }
}
/// Equality check against string literal (satisfies &ConnectionId == &str).
/// ```
/// use std::str::FromStr;
/// use ibc::ics24_host::identifier::ConnectionId;
/// let conn_id = ConnectionId::from_str("connectionId");
/// assert!(conn_id.is_ok());
/// conn_id.map(|id| {assert_eq!(&id, "connectionId")});
/// ```
impl PartialEq<str> for ConnectionId {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PortId(String);

impl PortId {
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
impl std::fmt::Display for PortId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for PortId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        validate_port_identifier(s).map(|_| Self(s.to_string()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ChannelId(String);

impl ChannelId {
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
impl std::fmt::Display for ChannelId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ChannelId {
    type Err = ValidationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        validate_channel_identifier(s).map(|_| Self(s.to_string()))
    }
}
