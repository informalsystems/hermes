use ibc_relayer_cosmos::types::payloads::{
    channel::{
        CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenTryPayload,
    },
    client::{CosmosCreateClientPayload, CosmosUpdateClientPayload},
};

pub enum SolomachineMessage {
    CosmosCreateClient(Box<CosmosCreateClientPayload>),
    CosmosUpdateClient(Box<CosmosUpdateClientPayload>),
    CosmosChannelOpenTry(Box<CosmosChannelOpenTryPayload>),
    CosmosChannelOpenAck(Box<CosmosChannelOpenAckPayload>),
    CosmosChannelOpenConfirm(Box<CosmosChannelOpenConfirmPayload>),
}
