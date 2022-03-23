//! Data structures and logic to set up IBC client's parameters.

use core::time::Duration;

use tendermint_light_client_verifier::types::TrustThreshold;

/// Client parameters for the `build_create_client` operation.
/// If set, the options override the defaults taken from the source chain configuration.
#[derive(Clone, Debug, Default)]
pub struct ClientSettings {
    pub max_clock_drift: Duration,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: TrustThreshold,
}
