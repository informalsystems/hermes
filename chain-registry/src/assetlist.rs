/// Contains models for serializing and deserializing `assets.json` for a given chain
// originally from https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/assets.rs
use crate::{
    error::RegistryError,
    utils::{fetch_data, FileName},
};
use serde::{Deserialize, Serialize};
use serde_json;

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

impl AssetList {
    pub async fn fetch(chain_name: String) -> Result<AssetList, RegistryError> {
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
    use super::*;
    // Consider adding a tests for a list of chains

    async fn fetch_cosmoshub_assets() {
        AssetList::fetch("cosmoshub").await.unwrap();
    }

    #[test]
    fn test_fetch_cosmoshub_assets() {
        use tokio::runtime::Runtime;
        let rt = Runtime::new().unwrap();
        rt.block_on(fetch_cosmoshub_assets());
    }
}
