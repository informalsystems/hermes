use crate::one_for_all::traits::chain::OfaChain;
use crate::traits::chain_context::ChainContext;
use crate::traits::message::{IbcMessage, Message};

pub struct OfaMessage<Chain: OfaChain> {
    pub message: Chain::Message,
}

impl<Chain: OfaChain> OfaMessage<Chain> {
    pub fn new(message: Chain::Message) -> Self {
        Self { message }
    }
}

impl<Chain: OfaChain> Message for OfaMessage<Chain> {
    type Signer = Chain::Signer;
    type RawMessage = Chain::RawMessage;
    type EncodeError = Chain::Error;

    fn encode_raw(&self, signer: &Self::Signer) -> Result<Self::RawMessage, Self::EncodeError> {
        Chain::encode_raw_message(&self.message, signer)
    }

    fn estimate_len(&self) -> Result<usize, Self::EncodeError> {
        Chain::estimate_message_len(&self.message)
    }
}

impl<Chain, Counterparty> IbcMessage<Counterparty> for OfaMessage<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    fn source_height(&self) -> Option<Counterparty::Height> {
        Chain::source_message_height(&self.message)
    }
}
