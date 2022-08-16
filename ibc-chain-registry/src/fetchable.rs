//! Contains the trait required to fetch and deserialize data from the chain repository
use crate::{
    constants::{DEFAULT_REF, HOST, PROTOCOL, REGISTRY_PATH},
    error::RegistryError,
};
use async_trait::async_trait;
use http::uri::Builder;
use serde::de::DeserializeOwned;
use std::path::PathBuf;

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
    async fn fetch(chain_name: String, commit: Option<String>) -> Result<Self, RegistryError> {
        let path = Self::path(chain_name.as_str());
        let url = Builder::new()
            .scheme(PROTOCOL)
            .authority(HOST)
            .path_and_query(
                format!(
                    "{}/{}/{}",
                    REGISTRY_PATH,
                    commit.unwrap_or_else(|| DEFAULT_REF.to_string()),
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
                    Err(e) => Err(RegistryError::json_parse_error(chain_name.to_string(), e)),
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
