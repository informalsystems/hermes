use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::traits::contexts::error::HasError;
use crate::traits::message::{IbcMessage, Message};

pub struct OfaMessage<Chain: OfaChain> {
    pub message: Chain::Message,
}

impl<Chain: OfaChain> OfaMessage<Chain> {
    pub fn new(message: Chain::Message) -> Self {
        Self { message }
    }
}

impl<Chain: OfaChain> HasError for OfaMessage<Chain> {
    type Error = Chain::Error;
}

impl<Chain: OfaChain> Message for OfaMessage<Chain> {
    type Signer = Chain::Signer;
    type RawMessage = Chain::RawMessage;

    fn encode_raw(&self, signer: &Self::Signer) -> Result<Self::RawMessage, Self::Error> {
        Chain::encode_raw_message(&self.message, signer)
    }

    fn estimate_len(&self) -> Result<usize, Self::Error> {
        Chain::estimate_message_len(&self.message)
    }
}

impl<Chain, Counterparty> IbcMessage<OfaChainContext<Counterparty>> for OfaMessage<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    fn source_height(&self) -> Option<Counterparty::Height> {
        Chain::source_message_height(&self.message)
    }
}
