use crate::traits::chain_context::ChainContext;
use crate::traits::core::Async;

pub trait Message: Async {
    type Signer;
    type RawMessage;
    type EncodeError;

    fn encode_raw(&self, signer: &Self::Signer) -> Result<Self::RawMessage, Self::EncodeError>;

    fn estimate_len(&self) -> Result<usize, Self::EncodeError>;
}

pub trait IbcMessage<Counterparty: ChainContext>: Message {
    fn source_height(&self) -> Option<Counterparty::Height>;
}
