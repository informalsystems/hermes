use crate::traits::chain_context::ChainContext;
use crate::types::aliases::Height;

pub trait Message {
    type Signer;
    type RawMessage;
    type EncodeError;

    fn encode_raw(self, signer: Self::Signer) -> Result<Self::RawMessage, Self::EncodeError>;
}

pub trait IbcMessage<Counterparty: ChainContext>: Message {
    fn source_height(&self) -> Option<Height<Counterparty>>;
}
