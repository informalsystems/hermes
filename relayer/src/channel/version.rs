use ibc::applications::ics20_fungible_token_transfer;
use ibc::applications::ics27_interchain_accounts;
use ibc::core::ics04_channel::Version;
use ibc::core::ics24_host::identifier::PortId;

use crate::channel::ChannelError;

/// Distinguishes between different steps of
/// the channel open handshake protocol, for use
/// in resolving channel versions.
///
/// We only need to distinguish between the OpenInit
/// step and all others.
pub enum HandshakeContext {
    ChanOpenInit,
    Other,
}

/// Resolves the [`ics04_channel::Version`] that should
/// be used during a channel open handshake, depending on
/// the channel handshake step.
pub fn resolve(step: HandshakeContext, port_id: &PortId) -> Result<Version, ChannelError> {
    match step {
        // Resolve by using the predefined application version.
        HandshakeContext::ChanOpenInit => {
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

        // Resolve the version by calling the destination chain
        HandshakeContext::Other => {
            todo!()
        }
    }
}
