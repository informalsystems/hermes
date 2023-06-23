use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::submit::CanSubmitTx;

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
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
