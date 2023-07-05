use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};

#[derive(Default)]
pub struct CosmosInitChannelOptions {
    pub port_id: PortId,
    pub counterparty_port_id: PortId,
    pub ordering: Ordering,
    pub connection_hops: Vec<ConnectionId>,
    pub channel_version: Version,
}

pub struct CosmosChannelOpenInitEvent {
    pub channel_id: ChannelId,
}
