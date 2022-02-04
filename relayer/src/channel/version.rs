//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

/// Returns the default channel version, for the given [`PortId`].
///
/// Currently only ICS20 and ICS27 ports are recognized.
pub fn default_by_port(port_id: &PortId) -> Option<Version> {
    match port_id.as_str() {
        ics20_fungible_token_transfer::PORT_ID => {
            // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
            Some(Version::ics20())
        }
        port_id if port_id.starts_with(ics27_interchain_accounts::PORT_ID_PREFIX) => {
            // https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#channel-lifecycle-management
            Some(Version::ics27())
        }
        _ => None,
    }
}
