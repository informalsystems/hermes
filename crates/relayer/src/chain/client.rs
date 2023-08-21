//! Data structures and logic to set up IBC client's parameters.

use std::time::Duration;

use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::chain::cosmos;
use crate::foreign_client::CreateOptions;

/// Client parameters for the `build_create_client` operation.
///
/// The parameters are specialized for each supported chain type.
#[derive(Clone, Debug)]
pub enum ClientSettings {
    Tendermint(cosmos::client::Settings),
}

impl ClientSettings {
    /// Takes the settings from the user-supplied options if they have been specified,
    /// falling back to defaults using the configuration of the source
    /// and the destination chain.
    pub fn for_create_command(
        options: CreateOptions,
        src_clock_drift: Duration,
        src_trust_threshold: TrustThreshold,
        dst_clock_drift: Duration,
        dst_max_block_time: Duration,
        dst_chain_id: &ChainId,
    ) -> Self {
        // Currently, only Tendermint chain pairs are supported by
        // ForeignClient::build_create_client_and_send. Support for
        // heterogeneous chains is left for future revisions.
        ClientSettings::Tendermint(cosmos::client::Settings::for_create_command(
            options,
            src_clock_drift,
            src_trust_threshold,
            dst_clock_drift,
            dst_max_block_time,
            dst_chain_id,
        ))
    }
}
