//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::{debug, warn};

use ibc::core::ics04_channel::channel::Counterparty;
use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

use crate::error::ErrorDetail;
use crate::{
    chain::handle::requests,
    chain::handle::ChainHandle,
    channel::{Channel, ChannelError},
    error::Error,
};

/// Defines the context in which to resolve a channel version.
///
/// This context distinguishes between different steps of
/// the channel open handshake protocol. Currently, we only
/// need to distinguish between the OpenInit & Open Try steps.
#[derive(Debug)]
pub enum ResolveContext {
    ChanOpenInit,
    ChanOpenTry,
}

/// Resolves the [`Version`] to use during a channel
/// open handshake.
///
/// The channel version depends on the exact channel
/// handshake step [`ResolveContext`], as well as
/// on the current state of the channel.
pub fn resolve<ChainA: ChainHandle, ChainB: ChainHandle>(
    ctx: ResolveContext,
    channel: &Channel<ChainA, ChainB>,
) -> Result<Version, ChannelError> {
    let port_id = channel.dst_port_id();

    match ctx {
        ResolveContext::ChanOpenInit => {
            // When the channel is uninitialized, the relayer will use the
            // default channel version, depending on the port id.
            default_by_port(port_id)
        }
        ResolveContext::ChanOpenTry => {
            // Resolve the version by querying the application version on destination chain
            let dst_chain_id = channel.dst_chain().id();
            debug!(chain_id = %dst_chain_id, port_id = %port_id, ctx = ?ctx, "resolving channel version by retrieving destination chain app version");

            // Note the compatibility logic below:
            // The destination chain may or may not implement `QueryAppVersionRequest`,
            // which is only available from ibc-go v2.0.0 or newer versions.
            // We detect if it is implemented by calling `is_unimplemented_port_query`.
            // If unimplemented, we can recover by simply using the default version.
            // This ensures compatibility with ibc-go v2.0.0+ and pre-v2.0.0.
            match dst_app_version(channel) {
                Ok(v) => Ok(v),
                Err(e) => {
                    if let ErrorDetail::GrpcStatus(s) = e.detail() {
                        if s.is_unimplemented_port_query() {
                            // Ensure compatibility & recover from the error,
                            // by using the default version.
                            debug!(chain_id = %dst_chain_id, "resorting to default version because destination chain does not expose app version gRPC endpoint");
                            return default_by_port(port_id);
                        }
                    }
                    // Propagate the error, this is not a recoverable problem.
                    Err(e).map_err(|e| ChannelError::query_app_version(channel.dst_chain().id(), e))
                }
            }
        }
    }
}

/// Returns the default channel version, depending on the
/// the given [`PortId`].
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
            "cannot resolve channel version for unknown port id '{}'",
            port_id,
        );
        Err(ChannelError::invalid_port_id(port_id.clone()))
    }
}

/// Fetches the application version from the destination
/// chain for the given [`Channel`].
fn dst_app_version<ChainA: ChainHandle, ChainB: ChainHandle>(
    channel: &Channel<ChainA, ChainB>,
) -> Result<Version, Error> {
    let counterparty = channel.src_channel_id().map(|cid| Counterparty {
        port_id: channel.src_port_id().clone(),
        channel_id: Some(cid.clone()),
    });

    let proposed_version = match channel.src_version() {
        Some(version) => Ok(version.clone()),
        None => {
            default_by_port(channel.src_port_id()).map_err(|e| Error::app_version(e.to_string()))
        }
    }?;

    debug!(
        "source channel end proposed version='{}'; original={:?}",
        proposed_version,
        channel.src_version()
    );

    let request = requests::AppVersion {
        port_id: channel.dst_port_id().clone(),
        connection_id: channel.dst_connection_id().clone(),
        ordering: channel.ordering,
        counterparty,
        proposed_version,
    };

    channel.dst_chain().app_version(request)
}
