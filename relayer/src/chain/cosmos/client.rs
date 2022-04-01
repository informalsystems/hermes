//! Cosmos-specific client settings.

use core::time::Duration;

use tracing::warn;

use ibc::core::ics02_client::trust_threshold::TrustThreshold;

use crate::config::ChainConfig;
use crate::foreign_client::CreateOptions;

/// Cosmos-specific client parameters for the `build_client_state` operation.
#[derive(Clone, Debug, Default)]
pub struct Settings {
    pub max_clock_drift: Duration,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: TrustThreshold,
}

impl Settings {
    pub fn for_create_command(
        options: CreateOptions,
        src_chain_config: &ChainConfig,
        dst_chain_config: &ChainConfig,
    ) -> Self {
        let max_clock_drift = match options.max_clock_drift {
            None => calculate_client_state_drift(src_chain_config, dst_chain_config),
            Some(user_value) => {
                if user_value > dst_chain_config.max_block_time {
                    warn!(
                        "user specified max_clock_drift ({:?}) exceeds max_block_time \
                        of the destination chain {}",
                        user_value, dst_chain_config.id,
                    );
                }
                user_value
            }
        };
        let trust_threshold = options
            .trust_threshold
            .unwrap_or_else(|| src_chain_config.trust_threshold.into());
        Settings {
            max_clock_drift,
            trusting_period: options.trusting_period,
            trust_threshold,
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
