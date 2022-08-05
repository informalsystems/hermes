use crate::error::RegistryError;
use http::uri::Builder;

pub const PROTOCOL: &str = "https";
pub const HOST: &str = "raw.githubusercontent.com";
pub const REGISTRY_PATH: &str = "/cosmos/chain-registry";
pub const REF: &str = "ffdfbff3a21c7d2dbaac6f1e4730f47063f4bd72";

pub const TEST_CHAINS : &[&str]= &["cosmoshub", "juno", "evmos", "osmosis", "regen"];

pub trait FileName {
    fn file_name() -> String;
}

pub async fn fetch_data<T: FileName>(chain_name: String) -> Result<String, RegistryError> {
    match Builder::new()
        .scheme(PROTOCOL)
        .authority(HOST)
        .path_and_query(
            format!(
                "{}/{}/{}/{}",
                REGISTRY_PATH,
                REF,
                chain_name,
                T::file_name()
            )
            .as_str(),
        )
        .build()
    {
        Ok(url) => match reqwest::get(url.to_string()).await {
            Ok(response) => match response.status().is_success() {
                true => match response.text().await {
                    Ok(body) => Ok(body),
                    Err(e) => Err(RegistryError::request_error(url.to_string(), e)),
                },
                _ => Err(RegistryError::status_error(
                    url.to_string(),
                    response.status().as_u16(),
                )),
            },
            Err(e) => Err(RegistryError::request_error(url.to_string(), e)),
        },
        Err(e) => Err(RegistryError::url_parse_error(chain_name.to_string(), e)), // Should be URL build error ?
    }
}
