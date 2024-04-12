//! Data structures and logic to set up IBC client's parameters.

use ibc_relayer_types::core::ics02_client::client_type::ClientType;

use crate::chain::cosmos::client::Settings as TendermintClientSettings;
use crate::config::ChainConfig;
use crate::foreign_client::{
    CreateOptions, TendermintCreateOptions, WasmCreateOptions, WasmUnderlyingCreateOptions,
};

#[derive(Clone, Debug)]
pub struct WasmClientSettings {
    pub checksum: Vec<u8>,
    pub underlying: WasmUnderlyingClientSettings,
}

#[derive(Clone, Debug)]
pub enum WasmUnderlyingClientSettings {
    Tendermint(TendermintClientSettings),
}

/// Client parameters for the `build_create_client` operation.
///
/// The parameters are specialized for each supported chain type.
#[derive(Clone, Debug)]
pub enum ClientSettings {
    Tendermint(TendermintClientSettings),
    Wasm(WasmClientSettings),
}

impl ClientSettings {
    pub fn client_type(&self) -> ClientType {
        match self {
            ClientSettings::Tendermint(_) => ClientType::Tendermint,
            ClientSettings::Wasm(_) => ClientType::Wasm,
        }
    }

    pub fn create(
        options: CreateOptions,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) -> Self {
        match options {
            CreateOptions::Tendermint(options) => {
                Self::create_tendermint(options, src_chain_config, dst_chain_config)
            }
            CreateOptions::Wasm(options) => {
                Self::create_wasm(options, src_chain_config, dst_chain_config)
            }
        }
    }

    /// Create the client settings for an ICS 07 Tendermint client between the given source and destination chains.
    /// Takes the settings from the user-supplied options if they have been specified,
    /// falling back to defaults using the configuration of the source and the destination chain.
    pub fn create_tendermint(
        options: TendermintCreateOptions,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) -> Self {
        // Currently, only Tendermint chain pairs are supported by
        // ForeignClient::build_create_client_and_send. Support for
        // heterogeneous chains is left for future revisions.
        //
        // TODO: extract Tendermint-related configs into a separate substructure
        // that can be used both by CosmosSdkConfig and configs for non-SDK chains.

        match (src_chain_config, dst_chain_config) {
            (
                ChainConfig::CosmosSdk(src_chain_config),
                ChainConfig::CosmosSdk(dst_chain_config),
            ) => ClientSettings::Tendermint(TendermintClientSettings::from_create_options(
                options,
                src_chain_config,
                dst_chain_config,
            )),
        }
    }

    /// Create the client settings for an ICS 08 Wasm client wrapping an ICS 07 Tendermint client
    /// between the given source and destination chains.
    /// Takes the settings from the user-supplied options if they have been specified,
    /// falling back to defaults using the configuration of the source and the destination chain.
    pub fn create_wasm(
        options: WasmCreateOptions,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) -> Self {
        // Currently, only Tendermint chain pairs are supported by
        // ForeignClient::build_create_client_and_send. Support for
        // heterogeneous chains is left for future revisions.
        //
        // TODO: extract Tendermint-related configs into a separate substructure
        // that can be used both by CosmosSdkConfig and configs for non-SDK chains.

        match (src_chain_config, dst_chain_config) {
            (
                ChainConfig::CosmosSdk(src_chain_config),
                ChainConfig::CosmosSdk(dst_chain_config),
            ) => {
                let settings = match options.underlying {
                    WasmUnderlyingCreateOptions::Tendermint(options) => {
                        TendermintClientSettings::from_create_options(
                            options,
                            src_chain_config,
                            dst_chain_config,
                        )
                    }
                };

                ClientSettings::Wasm(WasmClientSettings {
                    checksum: options.checksum,
                    underlying: WasmUnderlyingClientSettings::Tendermint(settings),
                })
            }
        }
    }
}
