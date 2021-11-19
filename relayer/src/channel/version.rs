//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::warn;

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::ics04_channel::Version,
};

use crate::{
    chain::handle::ChainHandle,
    channel::{Channel, ChannelError},
};

/// Defines the context in which to resolve a channel version.
///
/// This context distinguishes between different steps of
/// the channel open handshake protocol. Currently, we only
/// need to distinguish between the OpenInit step and any other.
pub enum ResolveContext {
    ChanOpenInit,
    Other,
}

/// Resolves the [`ics04_channel::Version`] that should
/// be used during a channel open handshake, depending on
/// the channel handshake step and the port identifier.
pub fn resolve<ChainA: ChainHandle, ChainB: ChainHandle>(
    ctx: ResolveContext,
    channel: &Channel<ChainA, ChainB>,
) -> Result<Version, ChannelError> {
    let port_id = channel.dst_port_id();

    match ctx {
        ResolveContext::ChanOpenInit => {
            // Resolve by using the predefined application version.
            if port_id.as_str() == ics20_fungible_token_transfer::PORT_ID {
                // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
                Ok(Version::from(ics20_fungible_token_transfer::VERSION))
            } else if port_id
                .as_str()
                .starts_with(ics27_interchain_accounts::PORT_ID_PREFIX)
            {
                // https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#channel-lifecycle-management
                Ok(Version::from(ics27_interchain_accounts::VERSION))
            } else {
                Err(ChannelError::invalid_port_id(port_id.clone()))
            }
        }

        ResolveContext::Other => {
            // Resolve the version by querying the application version on destination chain
            warn!("resolving channel version by calling destination chain");
            let request = channel.assemble_app_version_request();
            channel
                .dst_chain()
                .app_version(request)
                .map_err(|e| ChannelError::query(channel.dst_chain().id(), e))
        }
    }
}
