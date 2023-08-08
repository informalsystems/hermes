use ibc_relayer_types::core::ics24_host::identifier::ChannelId;

pub struct CosmosChannelOpenInitEvent {
    pub channel_id: ChannelId,
}
pub struct CosmosChannelOpenTryEvent {
    pub channel_id: ChannelId,
}
