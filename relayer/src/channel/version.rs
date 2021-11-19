//! Helper module for the relayer channel logic.
//!
//! Provides support for resolving the appropriate
//! channel version to be used in a channel open
//! handshake.

use tracing::info;

use ibc::{
    applications::{ics20_fungible_token_transfer, ics27_interchain_accounts},
    core::ics04_channel::Version,
};
use ibc::core::ics24_host::identifier::PortId;

use crate::{
    chain::handle::ChainHandle,
    channel::{Channel, ChannelError},
};
use crate::channel::error::ChannelErrorDetail;

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

/// Resolves the [`Version`] that should
/// be used during a channel open handshake, depending on
/// the channel handshake step [`ResolveContext`] as well as
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
            info!("resolving channel version for port id {}, context={:?} by retrieving destination chain app version", port_id, ctx);
            let result = channel.dst_app_version();

            // TODO(Adi): decide if to resort to default channel version here
            //  It's only safe to do so if we can match on the error sub detail:
            //      > gRPC call failed with status: status: Unimplemented, message: "unknown service ibc.core.port.v1.Query"
            //  then also change `validated_expected_channel` to call into `version::resolve` instead
            //  of calling `Channel::dst_version`.
            match result {
                Ok(v) => Ok(v),
                Err(e) if matches!(e.detail(), ChannelErrorDetail::Query(s)) => {
                    // if let ChannelErrorDetail::Query(s) = e.detail() {
                    //     if let v = s.source;
                        info!("error detail caught = {:?}", s);
                        Err(e)
                },
                Err(e) =>{
                        // Propagate the error, it's not a query problem.
                        Err(e)
                    }
                }
        }
    }
}

/// Returns the default channel version by port identifier.
fn default_by_port(port_id: &PortId) -> Result<Version, ChannelError> {
    if port_id.as_str() == ics20_fungible_token_transfer::PORT_ID {
        info!("resolving channel version for port id {} locally to {}", port_id, Version::ics20());
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer#forwards-compatibility
        Ok(Version::ics20())
    } else if port_id
        .as_str()
        .starts_with(ics27_interchain_accounts::PORT_ID_PREFIX)
    {
        info!("resolving channel version for port id {} locally to {}", port_id, Version::ics27());
        // https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#channel-lifecycle-management
        Ok(Version::ics27())
    } else {
        Err(ChannelError::invalid_port_id(port_id.clone()))
    }
}
