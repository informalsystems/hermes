//! Contains models for serializing and deserializing `assets.json` for a given chain
//! originally from https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/assets.rs
use crate::utils::Fetchable;

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

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

impl Fetchable for AssetList {
    fn path(resource: &str) -> PathBuf {
        [resource, "assetlist.json"].iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::RegistryError;
    use crate::utils::TEST_CHAINS;

    #[tokio::test]
    async fn test_fetch_chain_assets() -> Result<(), RegistryError> {
        let mut handles = Vec::with_capacity(TEST_CHAINS.len());
        for chain in TEST_CHAINS {
            handles.push(tokio::spawn(AssetList::fetch(chain.to_string())));
        }

        for handle in handles {
            handle.await.unwrap()?;
        }
        Ok(())
    }
}
