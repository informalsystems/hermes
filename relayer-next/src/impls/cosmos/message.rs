use ibc::signer::Signer;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use prost::EncodeError;

use crate::traits::chain_context::ChainContext;
use crate::traits::message::{IbcMessage, Message};

pub struct CosmosIbcMessage {
    pub source_height: Option<Height>,

    pub to_protobuf_fn: Box<dyn FnOnce(Signer) -> Result<Any, EncodeError> + 'static + Send + Sync>,
}

impl CosmosIbcMessage {
    pub fn new(
        source_height: Option<Height>,
        to_protobuf_fn: impl FnOnce(Signer) -> Result<Any, EncodeError> + 'static + Send + Sync,
    ) -> Self {
        Self {
            source_height,
            to_protobuf_fn: Box::new(to_protobuf_fn),
        }
    }
}

impl Message for CosmosIbcMessage {
    type Signer = Signer;
    type RawMessage = Any;
    type EncodeError = EncodeError;

    fn encode_raw(self, signer: Signer) -> Result<Any, EncodeError> {
        (self.to_protobuf_fn)(signer)
    }
}

impl<Counterparty> IbcMessage<Counterparty> for CosmosIbcMessage
where
    Counterparty: ChainContext<Height = Height>,
{
    fn source_height(&self) -> Option<Height> {
        self.source_height
    }
}
