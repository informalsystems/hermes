use async_trait::async_trait;

use super::chain_context::{ChainContext, IbcChainContext, IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSender<Counterparty: ChainContext>: IbcChainContext<Counterparty> {
    async fn send_message(
        &self,
        message: IbcMessage<Self, Counterparty>,
    ) -> Result<Vec<IbcEvent<Self, Counterparty>>, Self::Error>;
}
