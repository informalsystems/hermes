use async_trait::async_trait;

use crate::chain::traits::message_sender::MessageSender;
use crate::std_prelude::*;
use crate::transaction::traits::encode::CanEncodeTx;
use crate::transaction::traits::estimate::CanEstimateTxFee;
use crate::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::transaction::traits::fee::HasFeeForSimulation;
use crate::transaction::traits::message::{CanSendMessagesAsTx, MessageAsTxSender};
use crate::transaction::traits::nonce::CanAllocateNonce;
use crate::transaction::traits::response::CanPollTxResponse;
use crate::transaction::traits::signer::HasSigner;
use crate::transaction::traits::submit::CanSubmitTx;
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
        let response = chain
            .with_allocated_nonce(signer, &|nonce| {
                let messages_ref = &messages;
                Box::pin(async move {
                    chain
                        .send_messages_as_tx(signer, &nonce, messages_ref)
                        .await
                })
            })
            .await?;

        let events = Chain::parse_tx_response_as_events(response)?;

        Ok(events)
    }
}

#[async_trait]
impl<Context> MessageAsTxSender<Context> for SendMessagesAsTx
where
    Context: HasTxTypes
        + HasFeeForSimulation
        + CanEncodeTx
        + CanEstimateTxFee
        + CanSubmitTx
        + CanPollTxResponse,
{
    async fn send_messages_as_tx(
        context: &Context,
        signer: &Context::Signer,
        nonce: &Context::Nonce,
        messages: &[Context::Message],
    ) -> Result<Context::TxResponse, Context::Error> {
        let fee_for_simulation = context.fee_for_simulation();

        let simulate_tx = context
            .encode_tx(signer, nonce, fee_for_simulation, messages)
            .await?;

        let tx_fee = context.estimate_tx_fee(&simulate_tx).await?;

        let tx = context.encode_tx(signer, nonce, &tx_fee, messages).await?;

        let tx_hash = context.submit_tx(&tx).await?;

        let response = context.poll_tx_response(&tx_hash).await?;

        Ok(response)
    }
}
