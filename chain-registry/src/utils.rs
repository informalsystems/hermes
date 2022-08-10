use crate::error::RegistryError;
use async_trait::async_trait;
use http::uri::Builder;
use serde::de::DeserializeOwned;
use std::path::PathBuf;

pub const PROTOCOL: &str = "https";
pub const HOST: &str = "raw.githubusercontent.com";
pub const REGISTRY_PATH: &str = "/cosmos/chain-registry";
pub const REF: &str = "b246c965820890a2f659c6f2125a6a84f8c87379";

pub const ALL_CHAINS: &[&str] = &[
    "agoric",
    "aioz",
    "akash",
    "arkh",
    "assetmantle",
    "axelar",
    "bandchain",
    "bitcanna",
    "bitsong",
    "bostrom",
    "carbon",
    "cerberus",
    "cheqd",
    "chihuahua",
    "chronicnetwork",
    "comdex",
    "cosmoshub",
    "crescent",
    "cronos",
    "cryptoorgchain",
    "cudos",
    "decentr",
    "desmos",
    "dig",
    "echelon",
    "emoney",
    "ethos",
    "evmos",
    "fetchhub",
    "firmachain",
    "galaxy",
    "genesisl1",
    "gravitybridge",
    "idep",
    "impacthub",
    "injective",
    "irisnet",
    "juno",
    "kava",
    "kichain",
    "konstellation",
    "kujira",
    "likecoin",
    "logos",
    "lumenx",
    "lumnetwork",
    "meme",
    "microtick",
    "mythos",
    //"nomic", Does not have assetlist.json
    "octa",
    "odin",
    "omniflixhub",
    "oraichain",
    "osmosis",
    "panacea",
    "persistence",
    "provenance",
    "regen",
    "rizon",
    "secretnetwork",
    "sentinel",
    "shentu",
    "sifchain",
    "sommelier",
    "stargaze",
    "starname",
    "terra",
    "terra2",
    "tgrade",
    //"thorchain", Does not have assetlist.json
    "umee",
    "vidulum",
];

/// `Fetchable` represents the basic expectations for external data or resources that
/// can be fetched.
#[async_trait]
pub trait Fetchable
where
    Self: DeserializeOwned,
{
    /// The path of the fetchable resource.
    fn path(resource: &str) -> PathBuf;

    /// Fetches the fetchable resource.
    // The default implementation fetches config data from a chain registry. This
    // should be overridden if you're looking to fetch any other type of resource.
    async fn fetch(chain_name: String) -> Result<Self, RegistryError> {
        let path = Self::path(chain_name.as_str());
        let url = Builder::new()
            .scheme(PROTOCOL)
            .authority(HOST)
            .path_and_query(
                format!(
                    "{}/{}/{}",
                    REGISTRY_PATH,
                    REF,
                    path.clone()
                        .to_str()
                        .ok_or_else(|| RegistryError::path_error(path))?,
                )
                .as_str(),
            )
            .build()
            .map_err(|e| RegistryError::url_parse_error(chain_name.to_string(), e))?;

        let response = reqwest::get(url.to_string())
            .await
            .map_err(|e| RegistryError::request_error(url.to_string(), e))?;

        if response.status().is_success() {
            match response.text().await {
                Ok(body) => match serde_json::from_str(&body) {
                    Ok(parsed) => Ok(parsed),
                    Err(e) => Err(RegistryError::json_parse_error(e)),
                },
                Err(e) => Err(RegistryError::request_error(url.to_string(), e)),
            }
        } else {
            Err(RegistryError::status_error(
                url.to_string(),
                response.status().as_u16(),
            ))
        }
    }
}
