use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::encode::TxEncoder;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> TxEncoder<OfaTxWrapper<TxContext>> for OfaComponents
where
    TxContext: OfaTxContext,
{
    async fn encode_tx(
        context: &OfaTxWrapper<TxContext>,
        signer: &TxContext::Signer,
        nonce: &TxContext::Nonce,
        fee: &TxContext::Fee,
        messages: &[TxContext::Message],
    ) -> Result<TxContext::Transaction, TxContext::Error> {
        context
            .tx_context
            .encode_tx(signer, nonce, fee, messages)
            .await
    }
}
