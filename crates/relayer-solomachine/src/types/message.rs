use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenAckPayload;
use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenConfirmPayload;
use ibc_relayer_cosmos::types::payloads::channel::CosmosChannelOpenTryPayload;
use ibc_relayer_cosmos::types::payloads::client::CosmosCreateClientPayload;
use ibc_relayer_cosmos::types::payloads::client::CosmosUpdateClientPayload;
use ibc_relayer_cosmos::types::payloads::connection::CosmosConnectionOpenAckPayload;
use ibc_relayer_cosmos::types::payloads::connection::CosmosConnectionOpenConfirmPayload;
use ibc_relayer_cosmos::types::payloads::connection::CosmosConnectionOpenInitPayload;
use ibc_relayer_cosmos::types::payloads::connection::CosmosConnectionOpenTryPayload;

#[derive(Debug)]
pub enum SolomachineMessage {
    CosmosCreateClient(Box<CosmosCreateClientPayload>),
    CosmosUpdateClient(Box<CosmosUpdateClientPayload>),
    CosmosChannelOpenTry(Box<CosmosChannelOpenTryPayload>),
    CosmosChannelOpenAck(Box<CosmosChannelOpenAckPayload>),
    CosmosChannelOpenConfirm(Box<CosmosChannelOpenConfirmPayload>),
    CosmosConnectionOpenInit(Box<CosmosConnectionOpenInitPayload>),
    CosmosConnectionOpenTry(Box<CosmosConnectionOpenTryPayload>),
    CosmosConnectionOpenAck(Box<CosmosConnectionOpenAckPayload>),
    CosmosConnectionOpenConfirm(Box<CosmosConnectionOpenConfirmPayload>),
}
