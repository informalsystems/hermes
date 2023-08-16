use async_trait::async_trait;
use ibc_relayer_components::transaction::impls::message_sender::SendMessagesAsTx;
use ibc_relayer_components::transaction::traits::message::{
    CanSendMessagesAsTx, MessageAsTxSender,
};

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
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
