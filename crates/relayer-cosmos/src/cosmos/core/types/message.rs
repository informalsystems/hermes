use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

pub struct CosmosIbcMessage {
    pub source_height: Option<Height>,

    pub to_protobuf_fn: Box<dyn Fn(&Signer) -> Result<Any, EncodeError> + 'static + Send + Sync>,
}

impl CosmosIbcMessage {
    pub fn new(
        source_height: Option<Height>,
        to_protobuf_fn: impl Fn(&Signer) -> Result<Any, EncodeError> + 'static + Send + Sync,
    ) -> Self {
        Self {
            source_height,
            to_protobuf_fn: Box::new(to_protobuf_fn),
        }
    }
}
