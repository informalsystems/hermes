/// Models for serializing and deserializing IBC path JSON data found in the `_IBC/` directory of the registry repository
use crate::fetchable::Fetchable;
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

    use crate::constants::ALL_PATHS;

    #[tokio::test]
    #[ignore]
    async fn fetch_paths() -> Result<(), RegistryError> {
        let mut handles = Vec::with_capacity(ALL_PATHS.len());

        for resource in ALL_PATHS {
            handles.push(tokio::spawn(IBCPath::fetch(resource.to_string(), None)));
        }

        for handle in handles {
            let path: IBCPath = handle.await.unwrap()?;
            assert!(path.channels.len() > 0);
        }

        Ok(())
    }

    #[test]
    fn paths_path() {
        let path = IBCPath::path("test");
        assert_eq!(path, PathBuf::from("_IBC/test"));
    }

    #[test]
    fn paths_deserialize() {
        use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
        use std::str::FromStr;

        let path = r#"{
            "$schema": "http://json-schema.org/draft-07/schema#",
            "chain-1": {
                "chain-name": "chain-1",
                "client-id": "tendermint-1",
                "connection-id": "connection-1"
            },
            "chain-2": {
                "chain-name": "chain-2",
                "client-id": "tendermint-2",
                "connection-id": "connection-2"
            },
            "channels": [
                {
                    "chain-1": {
                        "channel-id": "channel-1",
                        "port-id": "port-1"
                    },
                    "chain-2": {
                        "channel-id": "channel-2",
                        "port-id": "port-2"
                    },
                    "ordering": "ordering",
                    "version": "version",
                    "tags": {
                        "dex": "dex",
                        "preferred": true,
                        "properties": "properties",
                        "status": "status"
                    }
                }
            ]
        }"#;
        let path: IBCPath = serde_json::from_str(path).unwrap();
        assert_eq!(path.schema, "http://json-schema.org/draft-07/schema#");
        assert_eq!(path.chain_1.chain_name, "chain-1");
        assert_eq!(
            path.chain_1.client_id,
            ClientId::from_str("tendermint-1").unwrap()
        );
        assert_eq!(
            path.chain_1.connection_id,
            ConnectionId::from_str("connection-1").unwrap()
        );
        assert_eq!(path.chain_2.chain_name, "chain-2");
        assert_eq!(
            path.chain_2.client_id,
            ClientId::from_str("tendermint-2").unwrap()
        );
        assert_eq!(
            path.chain_2.connection_id,
            ConnectionId::from_str("connection-2").unwrap()
        );
        assert_eq!(path.channels.len(), 1);
        assert_eq!(
            path.channels[0].chain_1.channel_id,
            ChannelId::from_str("channel-1").unwrap()
        );
        assert_eq!(
            path.channels[0].chain_1.port_id,
            PortId::from_str("port-1").unwrap()
        );
        assert_eq!(
            path.channels[0].chain_2.channel_id,
            ChannelId::from_str("channel-2").unwrap()
        );
        assert_eq!(
            path.channels[0].chain_2.port_id,
            PortId::from_str("port-2").unwrap()
        );
        assert_eq!(path.channels[0].ordering, "ordering");
        assert_eq!(path.channels[0].version, "version");
        assert_eq!(path.channels[0].tags.dex, "dex");
        assert_eq!(path.channels[0].tags.preferred, true);
        assert_eq!(path.channels[0].tags.properties, "properties");
        assert_eq!(path.channels[0].tags.status, "status");
    }
}
