use async_trait::async_trait;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::traits::submit::CanSubmitTx;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> CanSubmitTx for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error> {
        self.tx_context.submit_tx(tx).await
    }
}
