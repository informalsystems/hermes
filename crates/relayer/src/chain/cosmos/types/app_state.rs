//! Structure used to parse queried Genesis state using
//! /genesis RPC endpoint.

use serde::Deserialize as SerdeDeserialize;
use serde_derive::{
    Deserialize,
    Serialize,
};

#[derive(Debug, Deserialize, Serialize)]
pub struct GenesisAppState {
    ibc: IbcConfig,
}

impl GenesisAppState {
    pub fn max_expected_time_per_block(&self) -> u64 {
        self.ibc
            .connection_genesis
            .params
            .max_expected_time_per_block
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct IbcConfig {
    connection_genesis: ConnectionGenesisConfig,
}

#[derive(Debug, Deserialize, Serialize)]
struct ConnectionGenesisConfig {
    params: ConnectionGenesisParams,
}

#[derive(Debug, Deserialize, Serialize)]
struct ConnectionGenesisParams {
    #[serde(deserialize_with = "deserialize_max_expected_per_block")]
    max_expected_time_per_block: u64,
}

fn deserialize_max_expected_per_block<'de, T, D>(de: D) -> Result<T, D::Error>
where
    D: serde::Deserializer<'de>,
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: std::fmt::Display,
{
    String::deserialize(de)?
        .parse()
        .map_err(serde::de::Error::custom)
}
