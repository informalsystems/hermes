use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;

pub struct CosmosConnectionOpenInitEvent {
    pub connection_id: ConnectionId,
}

pub struct CosmosConnectionOpenTryEvent {
    pub connection_id: ConnectionId,
}
