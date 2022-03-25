//! Data structures and logic to set up IBC client's parameters.

use crate::chain::cosmos;
use crate::config::ChainConfig;

/// Client parameters for the `build_create_client` operation.
///
/// The parameters are specialized for each supported chain type.
#[derive(Clone, Debug)]
pub enum ClientSettings {
    Cosmos(cosmos::client::Settings),
}

impl ClientSettings {
    /// Fills in some settings if they have not been specified,
    /// using the configuration of the source and the destination chain.
    pub fn fill_in_from_chain_configs(
        &mut self,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) {
        use ClientSettings::*;

        match self {
            Cosmos(config) => config.fill_in_from_chain_configs(src_chain_config, dst_chain_config),
        }
    }
}
