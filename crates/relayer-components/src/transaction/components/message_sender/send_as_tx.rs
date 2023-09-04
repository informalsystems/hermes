use async_trait::async_trait;

use crate::chain::traits::components::message_sender::MessageSender;
use crate::std_prelude::*;
use crate::transaction::traits::components::message_as_tx_sender::CanSendMessagesAsTx;
use crate::transaction::traits::components::nonce_allocater::CanAllocateNonce;
use crate::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::transaction::traits::signer::HasSigner;
use crate::transaction::traits::types::HasTxTypes;

pub struct SendMessagesAsTx;

#[async_trait]
impl<Chain> MessageSender<Chain> for SendMessagesAsTx
where
    Chain: HasTxTypes
        + HasSigner
        + CanAllocateNonce
        + CanSendMessagesAsTx
        + CanParseTxResponseAsEvents,
{
    async fn send_messages(
        chain: &Chain,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error> {
        let signer = chain.get_signer();
        let nonce = chain.allocate_nonce(signer).await?;

        let response = chain
            .send_messages_as_tx(signer, Chain::deref_nonce(&nonce), &messages)
            .await?;

        let events = Chain::parse_tx_response_as_events(response)?;

        Ok(events)
    }
}
