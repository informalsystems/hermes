use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};

/// Defines the channel & port identifiers which comprise
/// the two ends of a relayer path.
pub struct PathIdentifiers {
    /// Channel & port ids on the target network, usually called the __destination__.
    pub port_id: PortId,
    pub channel_id: ChannelId,

    /// Channel & port ids on the counterparty network, often called the __source__.
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: ChannelId,
}

impl PathIdentifiers {
    pub fn from_channel_end(ice: IdentifiedChannelEnd) -> Option<Self> {
        let counterparty = ice.channel_end.remote;

        Some(Self {
            port_id: ice.port_id,
            channel_id: ice.channel_id,
            counterparty_port_id: counterparty.port_id,
            counterparty_channel_id: counterparty.channel_id?,
        })
    }
}
