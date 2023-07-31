use ibc_relayer_cosmos::types::payloads::client::{
    CosmosCreateClientPayload, CosmosUpdateClientPayload,
};

pub enum SolomachineMessage {
    CosmosCreateClient(Box<CosmosCreateClientPayload>),
    CosmosUpdateClient(Box<CosmosUpdateClientPayload>),
}
