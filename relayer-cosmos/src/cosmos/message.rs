use ibc::signer::Signer;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::traits::chain_context::ChainContext;
use ibc_relayer_framework::traits::message::{IbcMessage, Message};
use prost::{EncodeError, Message as _};

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

impl Message for CosmosIbcMessage {
    type Signer = Signer;
    type RawMessage = Any;
    type EncodeError = EncodeError;

    fn encode_raw(&self, signer: &Signer) -> Result<Any, EncodeError> {
        (self.to_protobuf_fn)(signer)
    }

    fn estimate_len(&self) -> Result<usize, Self::EncodeError> {
        let raw = (self.to_protobuf_fn)(&Signer::dummy())?;
        Ok(raw.encoded_len())
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
