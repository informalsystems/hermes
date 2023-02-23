use async_trait::async_trait;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;
use ibc_relayer_components::transaction::traits::encode::CanEncodeTx;

#[async_trait]
impl<TxContext> CanEncodeTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn encode_tx(
        &self,
        signer: &Self::Signer,
        nonce: &Self::Nonce,
        fee: &Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Self::Error> {
        self.tx_context
            .encode_tx(signer, nonce, fee, messages)
            .await
    }
}
