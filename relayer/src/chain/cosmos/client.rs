//! Cosmos-specific client settings.

use core::time::Duration;

use tendermint_light_client_verifier::types::TrustThreshold;

use crate::config::ChainConfig;

/// Cosmos-specific client parameters for the `build_create_client` operation.
/// If set, the options override the defaults taken from the source chain configuration.
#[derive(Clone, Debug, Default)]
pub struct Settings {
    pub max_clock_drift: Option<Duration>,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: Option<TrustThreshold>,
}

impl Settings {
    pub fn fill_in_from_chain_configs(
        &mut self,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) {
        if self.max_clock_drift.is_none() {
            self.max_clock_drift = Some(calculate_client_state_drift(
                &src_chain_config,
                &dst_chain_config,
            ));
        }
    }
}

/// The client state clock drift must account for destination
/// chain block frequency and clock drift on source and dest.
/// https://github.com/informalsystems/ibc-rs/issues/1445
fn calculate_client_state_drift(
    src_chain_config: &ChainConfig,
    dst_chain_config: &ChainConfig,
) -> Duration {
    src_chain_config.clock_drift + dst_chain_config.clock_drift + dst_chain_config.max_block_time
}
