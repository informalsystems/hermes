//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::debug;

use ibc::core::ics04_channel::channel::Counterparty;
use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};

use crate::{
    chain::handle::{requests, ChainHandle},
    channel::{error::ChannelErrorDetail, Channel, ChannelError},
    error::ErrorDetail,
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

    // Note the compatibility logic below:
    // The destination chain may or may not implement `QueryAppVersionRequest`,
    // which is only available from ibc-go v2.0.0 or newer versions.
    // We detect if it is implemented by calling `is_unimplemented_port_query`.
    // If unimplemented, we can recover by simply using the default version.
    // This ensures compatibility with ibc-go v2.0.0+ and pre-v2.0.0.
    match dst_app_version(channel) {
        Ok(v) => Ok(v),

        Err(e)
            if matches!(
                e.detail(),
                ChannelErrorDetail::AppVersionQueryUnsupported(_)
            ) =>
        {
            // Ensure compatibility & recover from the error, by using either the source version.
            debug!(
                chain = %dst_chain_id,
                "resorting to source version because destination chain does not expose the AppVersion gRPC endpoint"
            );

            channel.src_version().cloned().ok_or_else(|| {
                ChannelError::missing_source_version(
                    channel.src_chain().id(),
                    channel.src_channel_id().cloned(),
                )
            })
        }

        // Propagate the error, this is not a recoverable problem.
        Err(e) => Err(e),
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

/// Fetches the application version from the destination
/// chain for the given [`Channel`].
fn dst_app_version<ChainA: ChainHandle, ChainB: ChainHandle>(
    channel: &Channel<ChainA, ChainB>,
) -> Result<Version, ChannelError> {
    let counterparty = channel.src_channel_id().map(|cid| Counterparty {
        port_id: channel.src_port_id().clone(),
        channel_id: Some(cid.clone()),
    });

    let proposed_version = match channel.src_version() {
        Some(version) => Ok(version.clone()),
        None => default_by_port(channel.src_port_id()).ok_or_else(|| {
            ChannelError::missing_source_version(
                channel.dst_chain().id(),
                channel.src_channel_id().cloned(),
            )
        }),
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

    channel
        .dst_chain()
        .app_version(request)
        .map_err(|e| match e.detail() {
            ErrorDetail::GrpcStatus(s) if s.is_unimplemented_port_query() => {
                ChannelError::app_version_query_unsupported(channel.dst_chain().id())
            }
            _ => ChannelError::query_app_version(channel.dst_chain().id(), e),
        })
}
