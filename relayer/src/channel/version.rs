//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::{info, warn};

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::{ics04_channel::Version, ics24_host::identifier::PortId},
};
use ibc_proto::ibc::core::{channel::v1::Counterparty, port::v1::QueryAppVersionRequest};

use crate::error::ErrorDetail;
use crate::{
    chain::handle::ChainHandle,
    channel::{Channel, ChannelError},
    error::Error,
};

/// Defines the context in which to resolve a channel version.
///
/// This context distinguishes between different steps of
/// the channel open handshake protocol. Currently, we only
/// need to distinguish between the OpenInit step and any other.
#[derive(Debug)]
pub enum ResolveContext {
    ChanOpenInit,
    Other,
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
        ResolveContext::Other => {
            // Resolve the version by querying the application version on destination chain
            info!("resolving channel version for port id '{}', context={:?} by retrieving destination chain app version", port_id, ctx);

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
        info!(
            "resolving channel version for port id '{}' locally to {}",
            port_id,
            Version::ics20()
        );
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
        Ok(Version::ics20())
    } else if port_id
        .as_str()
        .starts_with(ics27_interchain_accounts::PORT_ID_PREFIX)
    {
        info!(
            "resolving channel version for port id '{}' locally to {}",
            port_id,
            Version::ics27()
        );
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
        port_id: channel.src_port_id().to_string(),
        channel_id: cid.to_string(),
    });

    let request = QueryAppVersionRequest {
        port_id: channel.dst_port_id().to_string(),
        connection_id: channel.dst_connection_id().to_string(),
        ordering: channel.ordering as i32,
        counterparty,
        proposed_version: Version::default().into(),
    };

    channel.dst_chain().app_version(request)
}
