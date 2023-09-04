use alloc::sync::Arc;
use core::fmt::Debug;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

pub trait CosmosMessage: Debug + Send + Sync + 'static {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        None
    }

    fn trusted_height(&self) -> Option<Height> {
        None
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError>;
}

pub trait ToCosmosMessage {
    fn to_cosmos_message(self) -> Arc<dyn CosmosMessage>;
}

impl<Message> ToCosmosMessage for Message
where
    Message: CosmosMessage,
{
    fn to_cosmos_message(self) -> Arc<dyn CosmosMessage> {
        Arc::new(self)
    }
}

pub fn wrap_cosmos_message<Message: CosmosMessage>(message: Message) -> Arc<dyn CosmosMessage> {
    Arc::new(message)
}
