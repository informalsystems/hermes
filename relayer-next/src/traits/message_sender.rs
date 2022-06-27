use async_trait::async_trait;

use crate::traits::chain_types::{ChainTypes, IbcChainTypes};
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSender<Chain, Counterparty>
where
    Chain: IbcChainTypes<Counterparty>,
    Counterparty: ChainTypes,
{
    async fn send_message(
        &self,
        message: IbcMessage<Chain, Counterparty>,
    ) -> Result<Vec<IbcEvent<Chain, Counterparty>>, Chain::Error>;

    async fn send_messages(
        &self,
        messages: Vec<IbcMessage<Chain, Counterparty>>,
    ) -> Result<Vec<Vec<IbcEvent<Chain, Counterparty>>>, Chain::Error>;

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [IbcMessage<Chain, Counterparty>; COUNT],
    ) -> Result<[Vec<IbcEvent<Chain, Counterparty>>; COUNT], Chain::Error>;
}
