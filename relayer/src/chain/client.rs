//! Data structures and logic to set up IBC client's parameters.

use core::time::Duration;

use tendermint_light_client_verifier::types::TrustThreshold;

use crate::config::ChainConfig;

/// Optional onfiguration parameters for the CreateClient command.
/// If set, the options override the defaults taken from the chain configuration.
#[derive(Clone, Debug, Default)]
pub struct ClientOptions {
    pub max_clock_drift: Option<Duration>,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: Option<TrustThreshold>,
}

/// The `max_clock_drift` value for a client state, computed as a function
/// of the configurations of the source chain and the destination chain.
///
/// The client state clock drift must account for destination
/// chain block frequency and clock drift on source and dest.
/// https://github.com/informalsystems/ibc-rs/issues/1445
pub fn calculate_clock_drift(
    src_chain_config: &ChainConfig,
    dst_chain_config: &ChainConfig,
) -> Duration {
    src_chain_config.clock_drift + dst_chain_config.clock_drift + dst_chain_config.max_block_time
}
