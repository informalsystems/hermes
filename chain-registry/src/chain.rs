/// Contains models for serializing and deserializing `chain.json` for a given chain
// Taken from https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/chain.rs
use crate::{
    error::RegistryError,
    utils::{fetch_data, FileName},
};
use serde::{Deserialize, Serialize};
use serde_json;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct ChainData {
    pub chain_name: String,
    pub status: String,
    pub network_type: String,
    pub pretty_name: String,
    pub chain_id: String,
    pub bech32_prefix: String,
    pub daemon_name: String,
    pub node_home: String,
    pub slip44: u32,
    pub genesis: Genesis,
    pub codebase: Codebase,
    pub peers: Peers,
    pub apis: Apis,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Genesis {
    pub genesis_url: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Codebase {
    pub git_repo: String,
    pub recommended_version: String,
    #[serde(skip_serializing_if = "Vec::is_empty", default = "Vec::new")]
    pub compatible_versions: Vec<String>,
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

impl FileName for ChainData {
    fn file_name() -> String {
        "chain.json".to_string()
    }
}

impl ChainData {
    pub async fn fetch(chain_name: String) -> Result<ChainData, RegistryError> {
        match fetch_data::<Self>(chain_name).await {
            Ok(body) => match serde_json::from_str(&body) {
                Ok(config) => Ok(config),
                Err(e) => Err(RegistryError::json_parse_error(e)),
            },
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::TEST_CHAINS;
    use super::*;

    async fn fetch_chain_data(chain : String) {
        ChainData::fetch(chain).await.unwrap();
    }

    #[test]
    fn test_fetch_chain_data() {
        use tokio::runtime::Runtime;
        let rt = Runtime::new().unwrap();

        let mut handles = Vec::with_capacity(TEST_CHAINS.len());
        for chain in TEST_CHAINS {
            handles.push(fetch_chain_data(chain.to_string()));
        }

        for handle in handles {
            rt.block_on(handle);
        }

    }
}
