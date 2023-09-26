//! Data structures and logic to set up IBC client's parameters.

use crate::chain::cosmos;
use crate::chain::near;
use crate::chain::ChainType;
use crate::config::ChainConfig;
use crate::foreign_client::CreateOptions;

/// Client parameters for the `build_create_client` operation.
///
/// The parameters are specialized for each supported chain type.
#[derive(Clone, Debug)]
pub enum ClientSettings {
    Tendermint(cosmos::client::Settings),
    Near(near::client::Settings),
}

impl ClientSettings {
    /// Takes the settings from the user-supplied options if they have been specified,
    /// falling back to defaults using the configuration of the source
    /// and the destination chain.
    pub fn for_create_command(
        options: CreateOptions,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) -> Self {
        match src_chain_config.r#type {
            ChainType::CosmosSdk => {
                // Currently, only Tendermint chain pairs are supported by
                // ForeignClient::build_create_client_and_send. Support for
                // heterogeneous chains is left for future revisions.
                ClientSettings::Tendermint(cosmos::client::Settings::for_create_command(
                    options,
                    src_chain_config,
                    dst_chain_config,
                ))
            }
            ChainType::Near => ClientSettings::Near(near::client::Settings::for_create_command(
                options,
                src_chain_config,
                dst_chain_config,
            )),
        }
    }

    pub fn cosmos_setting(self) -> Option<cosmos::client::Settings> {
        match self {
            ClientSettings::Tendermint(setting) => Some(setting),
            _ => None,
        }
    }

    pub fn near_setting(self) -> Option<near::client::Settings> {
        match self {
            ClientSettings::Near(setting) => Some(setting),
            _ => None,
        }
    }
}
