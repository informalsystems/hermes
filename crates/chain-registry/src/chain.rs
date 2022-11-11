//! Contains models for serializing and deserializing `chain.json` for a given chain
//! Taken from <https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/chain.rs>
use crate::fetchable::Fetchable;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct ChainData {
    #[serde(rename = "$schema")]
    pub schema: String,
    pub chain_name: String,
    pub status: String,
    pub network_type: String,
    pub pretty_name: String,
    pub chain_id: ChainId,
    pub bech32_prefix: String,
    pub daemon_name: String,
    pub node_home: String,
    pub genesis: Genesis,
    pub key_algos: Vec<String>,
    pub slip44: u32,
    pub fees: FeeTokens,
    pub staking: Staking,
    pub codebase: Codebase,
    pub peers: Peers,
    pub apis: Apis,
    #[serde(rename = "logo_URIs")]
    pub logo_uris: LogoURIs,
    pub keywords: Vec<String>,
}
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct LogoURIs {
    pub png: String,
    pub svg: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Token {
    pub denom: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Staking {
    pub staking_tokens: Vec<Token>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct FeeTokens {
    pub fee_tokens: Vec<FeeToken>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct FeeToken {
    pub denom: String,
    pub fixed_min_gas_price: f64,
    pub low_gas_price: f64,
    pub average_gas_price: f64,
    pub high_gas_price: f64,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Genesis {
    pub genesis_url: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Binaries {
    #[serde(rename = "linux/amd64")]
    pub linux_amd64: String,
    #[serde(rename = "linux/arm64")]
    pub linux_arm64: String,
    #[serde(rename = "darwin/amd64")]
    pub darwin_amd64: String,
    #[serde(rename = "windows/amd64")]
    pub windows_amd64: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Codebase {
    pub git_repo: String,
    pub recommended_version: String,
    #[serde(skip_serializing_if = "Vec::is_empty", default = "Vec::new")]
    pub compatible_versions: Vec<String>,
    pub binaries: Binaries,
    pub cosmos_sdk_version: String,
    pub tendermint_version: String,
    pub cosmwasm_version: String,
    pub cosmwasm_enabled: bool,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Peers {
    #[serde(skip_serializing_if = "Vec::is_empty", default = "Vec::new")]
    pub seeds: Vec<Seed>,
    pub persistent_peers: Vec<PersistentPeer>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Seed {
    pub id: String,
    pub address: String,
    pub provider: Option<String>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct PersistentPeer {
    pub id: String,
    pub address: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Apis {
    #[serde(skip_serializing_if = "Vec::is_empty", default = "Vec::new")]
    pub rpc: Vec<Rpc>,
    #[serde(skip_serializing_if = "Vec::is_empty", default = "Vec::new")]
    pub rest: Vec<Rest>,
    pub grpc: Vec<Grpc>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Rpc {
    pub address: String,
    pub provider: Option<String>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Rest {
    pub address: String,
    pub provider: Option<String>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Grpc {
    pub address: String,
    pub provider: Option<String>,
}

impl Fetchable for ChainData {
    fn path(ressource: &str) -> PathBuf {
        [ressource, "chain.json"].iter().collect()
    }
}

#[allow(clippy::bool_assert_comparison)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::ALL_CHAINS;
    use crate::error::RegistryError;

    #[tokio::test]
    #[ignore]
    async fn fetch_chain_data() -> Result<(), RegistryError> {
        let mut handles = Vec::with_capacity(ALL_CHAINS.len());
        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(ChainData::fetch(chain.to_string(), None)));
        }

        for handle in handles {
            handle.await.unwrap()?;
        }
        Ok(())
    }

    #[test]
    fn chain_data_path() {
        let path = ChainData::path("test");
        assert_eq!(path, PathBuf::from("test/chain.json"));
    }

    #[test]
    fn chain_data_deserialize() {
        use ibc_relayer_types::core::ics24_host::identifier::ChainId;
        use std::str::FromStr;
        let json = r#"{
            "$schema": "https://github.com/cosmos/chain-registry/blob/master/chain.schema.json",
            "chain_name": "test",
            "status": "active",
            "network_type": "test",
            "pretty_name": "test",
            "chain_id": "test-1",
            "bech32_prefix": "test",
            "daemon_name": "test",
            "node_home": "test",
            "slip44": 0,
            "fees": {
                "fee_tokens": [
                    {
                        "denom": "uosmo",
                        "fixed_min_gas_price": 0,
                        "low_gas_price": 0,
                        "average_gas_price": 0.025,
                        "high_gas_price": 0.04
                    }
                ]
            },
            "staking": {
                "staking_tokens": [
                    {
                        "denom": "uosmo"
                    }
                ]
            },
            "genesis": {
                "genesis_url": "test"
            },
            "codebase": {
                "git_repo": "test",
                "recommended_version": "test",
                "compatible_versions": ["test"],
                "binaries": {
                    "linux/amd64": "test",
                    "linux/arm64": "test",
                    "darwin/amd64": "test",
                    "windows/amd64": "test"
                },
                "cosmos_sdk_version": "0.45",
                "tendermint_version": "0.34",
                "cosmwasm_version": "0.24",
                "cosmwasm_enabled": true
            },
            "peers": {
                "seeds": [{
                    "id": "test",
                    "address": "test",
                    "provider": "test"
                }],
                "persistent_peers": [{
                    "id": "test",
                    "address": "test"
                }]
            },
            "apis": {
                "rpc": [{
                    "address": "test",
                    "provider": "test"
                }],
                "rest": [{
                    "address": "test",
                    "provider": "test"
                }],
                "grpc": [{
                    "address": "test",
                    "provider": "test"
                }]
            },
            "logo_URIs": {
                "png": "test",
                "svg": "test"
            },
            "keywords": [
                "foo", "bar", "foobar", "fubar", "beyond", "repair", "example"
            ]
        }"#;
        let chain_data = serde_json::from_str::<ChainData>(json).unwrap();
        assert_eq!(
            chain_data.schema,
            "https://github.com/cosmos/chain-registry/blob/master/chain.schema.json"
        );
        assert_eq!(chain_data.chain_name, "test");
        assert_eq!(chain_data.status, "active");
        assert_eq!(chain_data.network_type, "test");
        assert_eq!(chain_data.pretty_name, "test");
        assert_eq!(chain_data.chain_id, ChainId::from_str("test-1").unwrap());
        assert_eq!(chain_data.bech32_prefix, "test");
        assert_eq!(chain_data.daemon_name, "test");
        assert_eq!(chain_data.node_home, "test");
        assert_eq!(chain_data.slip44, 0);
        assert_eq!(chain_data.fees.fee_tokens.len(), 1);
        assert_eq!(chain_data.fees.fee_tokens[0].denom, "uosmo");
        assert_eq!(chain_data.fees.fee_tokens[0].fixed_min_gas_price, 0.0);
        assert_eq!(chain_data.fees.fee_tokens[0].low_gas_price, 0.0);
        assert_eq!(chain_data.fees.fee_tokens[0].average_gas_price, 0.025);
        assert_eq!(chain_data.fees.fee_tokens[0].high_gas_price, 0.04);
        assert_eq!(chain_data.staking.staking_tokens.len(), 1);
        assert_eq!(chain_data.staking.staking_tokens[0].denom, "uosmo");
        assert_eq!(chain_data.genesis.genesis_url, "test");
        assert_eq!(chain_data.codebase.git_repo, "test");
        assert_eq!(chain_data.codebase.recommended_version, "test");
        assert_eq!(chain_data.codebase.compatible_versions[0], "test");
        assert_eq!(chain_data.codebase.binaries.linux_amd64, "test");
        assert_eq!(chain_data.codebase.binaries.linux_arm64, "test");
        assert_eq!(chain_data.codebase.binaries.darwin_amd64, "test");
        assert_eq!(chain_data.codebase.binaries.windows_amd64, "test");
        assert_eq!(chain_data.codebase.cosmos_sdk_version, "0.45");
        assert_eq!(chain_data.codebase.tendermint_version, "0.34");
        assert_eq!(chain_data.codebase.cosmwasm_version, "0.24");
        assert_eq!(chain_data.codebase.cosmwasm_enabled, true);
        assert_eq!(chain_data.peers.seeds[0].id, "test");
        assert_eq!(chain_data.peers.seeds[0].address, "test");
        assert_eq!(chain_data.peers.seeds[0].provider, Some("test".to_string()));
        assert_eq!(chain_data.peers.persistent_peers[0].id, "test");
        assert_eq!(chain_data.peers.persistent_peers[0].address, "test");
        assert_eq!(chain_data.apis.rpc[0].address, "test");
        assert_eq!(chain_data.apis.rpc[0].provider, Some("test".to_string()));
        assert_eq!(chain_data.apis.rest[0].address, "test");
        assert_eq!(chain_data.apis.rest[0].provider, Some("test".to_string()));
        assert_eq!(chain_data.apis.grpc[0].address, "test");
        assert_eq!(chain_data.apis.grpc[0].provider, Some("test".to_string()));
    }
}
