use super::chain_context::{ChainContext, Height};

pub trait IbcMessage<Counterparty: ChainContext> {
    type Signer;
    type RawMessage;
    type EncodeError;

    fn source_height(&self) -> Height<Counterparty>;

    fn encode_raw(self, signer: Self::Signer) -> Result<Self::RawMessage, Self::EncodeError>;
}
