use ibc_relayer_cosmos::types::payloads::client::{
    CosmosCreateClientPayload, CosmosUpdateClientPayload,
};

pub enum SolomachineMessage {
    CosmosCreateClient(CosmosCreateClientPayload),
    CosmosUpdateClient(CosmosUpdateClientPayload),
}
