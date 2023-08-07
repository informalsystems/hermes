use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenAckPayload;
use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenConfirmPayload;
use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenTryPayload;
use ibc_relayer_cosmos::types::payloads::client::CosmosCreateClientPayload;
use ibc_relayer_cosmos::types::payloads::client::CosmosUpdateClientPayload;

pub enum SolomachineMessage {
    CosmosCreateClient(Box<CosmosCreateClientPayload>),
    CosmosUpdateClient(Box<CosmosUpdateClientPayload>),
    CosmosChannelOpenTry(Box<CosmosChannelOpenTryPayload>),
    CosmosChannelOpenAck(Box<CosmosChannelOpenAckPayload>),
    CosmosChannelOpenConfirm(Box<CosmosChannelOpenConfirmPayload>),
}
