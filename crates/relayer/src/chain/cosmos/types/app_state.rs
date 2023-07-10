//! Structure used to parse queried Genesis state using
//! /genesis RPC endpoint.

use serde_derive::Deserialize;
use serde_derive::Serialize;
use serde_with::serde_as;
use serde_with::DisplayFromStr;

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

#[serde_as]
#[derive(Debug, Deserialize, Serialize)]
struct ConnectionGenesisParams {
    #[serde_as(as = "DisplayFromStr")]
    max_expected_time_per_block: u64,
}
