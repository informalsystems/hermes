use async_trait::async_trait;

use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSender<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    async fn send_message(
        &self,
        message: IbcMessage<Self, Counterparty>,
    ) -> Result<Vec<IbcEvent<Self, Counterparty>>, Self::Error>;

    async fn send_messages(
        &self,
        messages: Vec<IbcMessage<Self, Counterparty>>,
    ) -> Result<Vec<Vec<IbcEvent<Self, Counterparty>>>, Self::Error>;
}
