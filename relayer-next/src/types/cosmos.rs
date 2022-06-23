use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::handle::ChainHandle;
use prost::EncodeError;

use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::message::{IbcMessage, Message};
use crate::types::error::Error;

pub struct CosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
}

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

impl<Handle: ChainHandle> ChainContext for CosmosChainContext<Handle> {
    type Error = Error;

    type Height = Height;
    type Timestamp = Timestamp;
    type Message = CosmosIbcMessage;
}

impl<Handle: ChainHandle, Counterparty> IbcChainContext<Counterparty> for CosmosChainContext<Handle>
where
    Counterparty: ChainContext<Height = Height>,
{
    type ChannelId = ChannelId;
    type PortId = PortId;
    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;
    type IbcEvent = IbcEvent;
}
