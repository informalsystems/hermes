//! Contains models for serializing and deserializing `assets.json` for a given chain
//! originally from https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/assets.rs
use crate::utils::{Fetch, FileName};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct AssetList {
    pub chain_name: String,
    pub assets: Vec<Asset>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct Asset {
    pub description: String,
    pub denom_units: Vec<DenomUnit>,
    pub base: String,
    pub name: String,
    pub display: String,
    pub symbol: String,
    #[serde(rename = "logo_URIs")]
    pub logo_uris: LogoURIs,
    pub coingecko_id: String,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct DenomUnit {
    pub denom: String,
    pub exponent: u16,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct LogoURIs {
    pub png: String,
    pub svg: String,
}
impl FileName for AssetList {
    fn file_name() -> String {
        "assetlist.json".to_string()
    }
}

impl Fetch<AssetList> for AssetList {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::TEST_CHAINS;

    async fn fetch_chain_assets(chain: String) {
        AssetList::fetch(chain).await.unwrap();
    }

    #[test]
    fn test_fetch_chain_assets() {
        use tokio::runtime::Runtime;
        let rt = Runtime::new().unwrap();

        let mut handles = Vec::with_capacity(TEST_CHAINS.len());
        for chain in TEST_CHAINS {
            handles.push(fetch_chain_assets(chain.to_string()));
        }

        for handle in handles {
            rt.block_on(handle);
        }
    }
}
