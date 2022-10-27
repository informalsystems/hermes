use async_trait::async_trait;

use crate::base::transaction::traits::encode::CanEncodeTx;
use crate::base::transaction::traits::estimate::CanEstimateTxFee;
use crate::base::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::base::transaction::traits::fee::HasMaxFee;
use crate::base::transaction::traits::message::MessageAsTxSender;
use crate::base::transaction::traits::response::CanPollTxResponse;
use crate::base::transaction::traits::submit::CanSubmitTx;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub struct SendMessagesAsTx;

pub trait InjectNoTxResponseError: HasTxTypes {
    fn inject_tx_no_response_error(tx_hash: Self::TxHash) -> Self::Error;
}

#[async_trait]
impl<Context> MessageAsTxSender<Context> for SendMessagesAsTx
where
    Context: HasTxTypes
        + InjectNoTxResponseError
        + HasMaxFee
        + CanEncodeTx
        + CanEstimateTxFee
        + CanSubmitTx
        + CanPollTxResponse
        + CanParseTxResponseAsEvents,
{
    async fn send_messages_as_tx(
        context: &Context,
        nonce: &Context::Nonce,
        messages: &[Context::Message],
    ) -> Result<Context::TxResponse, Context::Error> {
        let max_fee = context.max_fee();

        let simulate_tx = context.encode_tx(nonce, max_fee, &messages).await?;

        let tx_fee = context.estimate_tx_fee(&simulate_tx).await?;

        let tx = context.encode_tx(nonce, &tx_fee, &messages).await?;

        let tx_hash = context.submit_tx(&tx).await?;

        let response = context.poll_tx_response(&tx_hash).await?;

        Ok(response)
    }
}
