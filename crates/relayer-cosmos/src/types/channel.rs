use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ConnectionId};
use ibc_relayer_types::proofs::Proofs;

#[derive(Default)]
pub struct CosmosInitChannelOptions {
    pub ordering: Ordering,
    pub connection_hops: Vec<ConnectionId>,
    pub channel_version: Version,
}

pub struct CosmosChannelOpenTryPayload {
    pub previous_channel_id: Option<ChannelId>,
    pub proofs: Proofs,
    pub ordering: Ordering,
    pub connection_hops: Vec<ConnectionId>,
    pub version: Version,
}

pub struct CosmosChannelOpenAckPayload {
    pub proofs: Proofs,
    pub version: Version,
}

pub struct CosmosChannelOpenInitEvent {
    pub channel_id: ChannelId,
}
pub struct CosmosChannelOpenTryEvent {
    pub channel_id: ChannelId,
}
