//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::warn;

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

use crate::channel::ChannelError;

/// Returns the default channel version, depending on the the given [`PortId`].
pub fn default_by_port(port_id: &PortId) -> Result<Version, ChannelError> {
    if port_id.as_str() == ics20_fungible_token_transfer::PORT_ID {
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
        Ok(Version::ics20())
    } else if port_id
        .as_str()
        .starts_with(ics27_interchain_accounts::PORT_ID_PREFIX)
    {
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#channel-lifecycle-management
        Ok(Version::ics27())
    } else {
        warn!(
            port = %port_id,
            "cannot resolve channel version for unknown port",
        );

        Err(ChannelError::invalid_port_id(port_id.clone()))
    }
}
