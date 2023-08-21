//! Cosmos-specific client settings.

use core::time::Duration;

use tracing::warn;

use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::foreign_client::CreateOptions;
use crate::util::pretty::PrettyDuration;

/// Cosmos-specific client parameters for the `build_client_state` operation.
#[derive(Copy, Clone, Debug, Default)]
pub struct Settings {
    pub max_clock_drift: Duration,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: TrustThreshold,
}

impl Settings {
    pub fn for_create_command(
        options: CreateOptions,
        src_clock_drift: Duration,
        src_trust_threshold: TrustThreshold,
        dst_clock_drift: Duration,
        dst_max_block_time: Duration,
        dst_chain_id: &ChainId,
    ) -> Self {
        let max_clock_drift = match options.max_clock_drift {
            None => {
                calculate_client_state_drift(src_clock_drift, dst_clock_drift, dst_max_block_time)
            }
            Some(user_value) => {
                if user_value > dst_max_block_time {
                    warn!(
                        "user specified max_clock_drift ({}) exceeds max_block_time \
                        of the destination chain {}",
                        PrettyDuration(&user_value),
                        dst_chain_id,
                    );
                }
                user_value
            }
        };

        Settings {
            max_clock_drift,
            trusting_period: options.trusting_period,
            trust_threshold: options
                .trust_threshold
                .unwrap_or_else(|| src_trust_threshold.into()),
        }
    }
}

/// The client state clock drift must account for destination
/// chain block frequency and clock drift on source and dest.
/// https://github.com/informalsystems/hermes/issues/1445
fn calculate_client_state_drift(
    src_clock_drift: Duration,
    dst_clock_drift: Duration,
    dst_max_block_time: Duration,
) -> Duration {
    src_clock_drift + dst_clock_drift + dst_max_block_time
}
