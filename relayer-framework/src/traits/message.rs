use crate::traits::contexts::chain::ChainContext;
use crate::traits::contexts::error::HasError;

pub trait Message: HasError {
    type Signer;
    type RawMessage;

    fn encode_raw(&self, signer: &Self::Signer) -> Result<Self::RawMessage, Self::Error>;

    fn estimate_len(&self) -> Result<usize, Self::Error>;
}

pub trait IbcMessage<Counterparty: ChainContext>: Message {
    fn source_height(&self) -> Option<Counterparty::Height>;
}
