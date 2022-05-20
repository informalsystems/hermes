//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use ibc::{
    applications::transfer,
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

/// Returns the default channel version, depending on the the given [`PortId`].
pub fn default_by_port(port_id: &PortId) -> Option<Version> {
    if port_id.as_str() == transfer::PORT_ID_STR {
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
        Some(Version::ics20())
    } else {
        None
    }
}
