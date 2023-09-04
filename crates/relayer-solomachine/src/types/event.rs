use ibc_relayer_types::{
    clients::ics07_tendermint::client_state::ClientState,
    core::ics24_host::identifier::{ClientId, ConnectionId},
};

pub enum SolomachineEvent {
    ConnectionInit(SolomachineConnectionInitEvent),
    CreateClient(SolomachineCreateClientEvent),
}

pub struct SolomachineCreateClientEvent {
    pub client_id: ClientId,
    pub client_state: ClientState,
}

pub struct SolomachineConnectionInitEvent {
    pub connection_id: ConnectionId,
}
