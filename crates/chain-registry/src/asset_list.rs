//! Contains models for serializing and deserializing `assets.json` for a given chain
//! originally from <https://github.com/PeggyJV/ocular/blob/main/ocular/src/registry/assets.rs>

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

use crate::fetchable::Fetchable;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default)]
pub struct AssetList {
    #[serde(rename = "$schema")]
    pub schema: String,
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
    use crate::constants::ALL_CHAINS;
    use crate::error::RegistryError;

    #[tokio::test]
    #[ignore]
    async fn fetch_chain_assets() -> Result<(), RegistryError> {
        let mut handles = Vec::with_capacity(ALL_CHAINS.len());
        for chain in ALL_CHAINS {
            handles.push(tokio::spawn(AssetList::fetch(chain.to_string(), None)));
        }

        for handle in handles {
            handle.await.unwrap()?;
        }
        Ok(())
    }

    #[test]
    fn asset_list_path() {
        let path = AssetList::path("test");
        assert_eq!(path.to_str().unwrap(), "test/assetlist.json");
    }

    #[test]
    fn asset_list_deserialize() {
        let json = r#"{
            "$schema": "https://github.com/cosmos/chain-registry/blob/master/assetlist.schema.json",
            "chain_name": "test",
            "assets": [
                {
                    "description": "test",
                    "denom_units": [
                        {
                            "denom": "test",
                            "exponent": 1
                        }
                    ],
                    "base": "test",
                    "name": "test",
                    "display": "test",
                    "symbol": "test",
                    "logo_URIs": {
                        "png": "test",
                        "svg": "test"
                    },
                    "coingecko_id": "test"
                }
            ]
        }"#;
        let asset_list: AssetList = serde_json::from_str(json).unwrap();
        assert_eq!(
            asset_list.schema,
            "https://github.com/cosmos/chain-registry/blob/master/assetlist.schema.json"
        );
        assert_eq!(asset_list.chain_name, "test");
        assert_eq!(asset_list.assets.len(), 1);
        assert_eq!(asset_list.assets[0].description, "test");
        assert_eq!(asset_list.assets[0].denom_units.len(), 1);
        assert_eq!(asset_list.assets[0].denom_units[0].denom, "test");
        assert_eq!(asset_list.assets[0].denom_units[0].exponent, 1);
        assert_eq!(asset_list.assets[0].base, "test");
        assert_eq!(asset_list.assets[0].name, "test");
        assert_eq!(asset_list.assets[0].display, "test");
        assert_eq!(asset_list.assets[0].symbol, "test");
        assert_eq!(asset_list.assets[0].logo_uris.png, "test");
        assert_eq!(asset_list.assets[0].logo_uris.svg, "test");
        assert_eq!(asset_list.assets[0].coingecko_id, "test");
    }
}
