use async_trait::async_trait;

use crate::base::chain::traits::message_sender::MessageSender;
use crate::base::chain::traits::types::HasChainTypes;
use crate::base::transaction::traits::encode::CanEncodeTx;
use crate::base::transaction::traits::estimate::CanEstimateTxFee;
use crate::base::transaction::traits::event::CanParseTxResponseAsEvents;
use crate::base::transaction::traits::fee::HasMaxFee;
use crate::base::transaction::traits::nonce::HasNonce;
use crate::base::transaction::traits::response::CanQueryTxResponse;
use crate::base::transaction::traits::submit::CanSubmitTx;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub struct SendMessagesAsTx;

pub trait InjectNoTxResponseError: HasTxTypes {
    fn inject_tx_no_response_error(tx_hash: Self::TxHash) -> Self::Error;
}

#[async_trait]
impl<Chain> MessageSender<Chain> for SendMessagesAsTx
where
    Chain: HasChainTypes
        + HasTxTypes
        + InjectNoTxResponseError
        + HasMaxFee
        + HasNonce
        + CanEncodeTx
        + CanEstimateTxFee
        + CanSubmitTx
        + CanQueryTxResponse
        + CanParseTxResponseAsEvents,
{
    async fn send_messages(
        chain: &Chain,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error> {
        let max_fee = chain.max_fee();
        chain
            .with_nonce(|nonce| {
                Box::pin(async {
                    let simulate_tx = chain.encode_tx(nonce, max_fee, &messages).await?;

                    let tx_fee = chain.estimate_tx_fee(&simulate_tx).await?;

                    let tx = chain.encode_tx(nonce, &tx_fee, &messages).await?;

                    let tx_hash = chain.submit_tx(&tx).await?;

                    let response = chain
                        .query_tx_response(&tx_hash)
                        .await?
                        .ok_or_else(|| Chain::inject_tx_no_response_error(tx_hash))?;

                    let events = Chain::parse_tx_response_as_events(response)?;

                    Ok(events)
                })
            })
            .await
    }
}
