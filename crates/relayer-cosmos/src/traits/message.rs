use alloc::sync::Arc;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

pub trait CosmosMessage: Send + Sync + 'static {
    fn counterparty_height(&self) -> Option<Height>;

    fn trusted_height(&self) -> Option<Height>;

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError>;
}

pub fn wrap_cosmos_message<Message: CosmosMessage>(message: Message) -> Arc<dyn CosmosMessage> {
    Arc::new(message)
}
