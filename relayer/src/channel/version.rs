//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::debug;

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

use crate::{
    chain::handle::ChainHandle,
    channel::{Channel, ChannelError},
};

/// Resolves the [`Version`] to use during a channel open try step of the handshake.
pub fn resolve<ChainA: ChainHandle, ChainB: ChainHandle>(
    channel: &Channel<ChainA, ChainB>,
) -> Result<Version, ChannelError> {
    let port_id = channel.dst_port_id();

    // Resolve the version by querying the application version on destination chain
    let dst_chain_id = channel.dst_chain().id();

    debug!(
        chain = %dst_chain_id,
        port = %port_id,
        "resolving channel version by retrieving destination chain app version"
    );

    match channel.src_version() {
        Some(version) => Ok(version.clone()),
        None => default_by_port(channel.src_port_id()).ok_or_else(|| {
            ChannelError::missing_source_version(
                channel.dst_chain().id(),
                channel.src_channel_id().cloned(),
            )
        }),
    }
}

/// Returns the default channel version, depending on the the given [`PortId`].
pub fn default_by_port(port_id: &PortId) -> Option<Version> {
    if port_id.as_str() == ics20_fungible_token_transfer::PORT_ID {
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
        Some(Version::ics20())
    } else if port_id
        .as_str()
        .starts_with(ics27_interchain_accounts::PORT_ID_PREFIX)
    {
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#channel-lifecycle-management
        Some(Version::ics27())
    } else {
        None
    }
}
