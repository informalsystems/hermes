use async_trait::async_trait;

use crate::base::chain::traits::message_sender::{CanSendMessages, MessageSender};
use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::impls::message_sender::SendMessagesAsTx;
use crate::base::transaction::traits::message::{CanSendMessagesAsTx, MessageAsTxSender};
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> CanSendMessagesAsTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn send_messages_as_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        messages: &[Self::Message],
    ) -> Result<Self::TxResponse, Self::Error> {
        SendMessagesAsTx::send_messages_as_tx(self, signer, nonce, messages).await
    }
}

#[async_trait]
impl<TxContext> CanSendMessages for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        SendMessagesAsTx::send_messages(self, messages).await
    }
}
