use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer_components::chain::traits::components::message_sender::{
    CanSendMessages, MessageSender,
};
use tendermint::abci::Event as AbciEvent;

use crate::contexts::transaction::CosmosTxContext;
use crate::traits::message::CosmosMessage;
use crate::types::error::Error;

pub struct CosmosTxInstances;

// Proof that CosmosTxContext implements [`CanSendMessages`].
#[async_trait]
impl MessageSender<CosmosTxContext> for CosmosTxInstances {
    async fn send_messages(
        tx_context: &CosmosTxContext,
        messages: Vec<Arc<dyn CosmosMessage>>,
    ) -> Result<Vec<Vec<Arc<AbciEvent>>>, Error> {
        tx_context.send_messages(messages).await
    }
}
