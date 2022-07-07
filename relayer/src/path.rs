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

// TODO: This should probably be a `TryFrom` instead of `From` so we can get rid of `expect`.
// TODO: Clarify if we should keep `From<&..>` or `From<..>.
impl From<&IdentifiedChannelEnd> for PathIdentifiers {
    fn from(ice: &IdentifiedChannelEnd) -> Self {
        let counterparty = ice.channel_end.counterparty();
        let counterparty_channel_id = counterparty
            .channel_id()
            .expect("no channel identifier in counterparty channel end");

        Self {
            port_id: ice.port_id.clone(),
            channel_id: ice.channel_id.clone(),
            counterparty_port_id: counterparty.port_id.clone(),
            counterparty_channel_id: counterparty_channel_id.clone(),
        }
    }
}
