/// Models for serializing and deserializing IBC path JSON data found in the `_IBC/` directory of the registry repository
use crate::utils::Fetchable;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use serde::Deserialize;
use serde::Serialize;
use std::path::PathBuf;

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct IBCPath {
    #[serde(rename = "$schema")]
    pub schema: String,
    #[serde(rename = "chain-1")]
    pub chain_1: Chain1,
    #[serde(rename = "chain-2")]
    pub chain_2: Chain2,
    pub channels: Vec<Channel>,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct Chain1 {
    #[serde(rename = "chain-name")]
    pub chain_name: String,
    #[serde(rename = "client-id")]
    pub client_id: ClientId,
    #[serde(rename = "connection-id")]
    pub connection_id: ConnectionId,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct Chain2 {
    #[serde(rename = "chain-name")]
    pub chain_name: String,
    #[serde(rename = "client-id")]
    pub client_id: ClientId,
    #[serde(rename = "connection-id")]
    pub connection_id: ConnectionId,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct Channel {
    #[serde(rename = "chain-1")]
    pub chain_1: ChannelChain1,
    #[serde(rename = "chain-2")]
    pub chain_2: ChannelChain2,
    pub ordering: String,
    pub version: String,
    pub tags: Tags,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct ChannelChain1 {
    #[serde(rename = "channel-id")]
    pub channel_id: ChannelId,
    #[serde(rename = "port-id")]
    pub port_id: PortId,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct ChannelChain2 {
    #[serde(rename = "channel-id")]
    pub channel_id: ChannelId,
    #[serde(rename = "port-id")]
    pub port_id: PortId,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct Tags {
    pub dex: String,
    pub preferred: bool,
    pub properties: String,
    pub status: String,
}

/// Represents an IBC path tag
pub enum Tag {
    Dex(String),
    Preferred(bool),
    Properties(String),
    Status(String),
}

impl Fetchable for IBCPath {
    fn path(resource: &str) -> PathBuf {
        ["_IBC", resource].iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::RegistryError;

    use crate::utils::ALL_PATHS;

    #[tokio::test]
    async fn fetch_paths() -> Result<(), RegistryError> {
        let mut handles = Vec::with_capacity(ALL_PATHS.len());
        for resource in ALL_PATHS {
            handles.push(tokio::spawn(IBCPath::fetch(resource.to_string())));
        }

        for handle in handles {
            let path: IBCPath = handle.await.unwrap()?;
            assert!(path.channels.len() > 0);
        }
        Ok(())
    }
}
