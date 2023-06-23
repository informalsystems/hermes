use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::estimate::CanEstimateTxFee;

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> CanEstimateTxFee for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error> {
        self.tx_context.estimate_tx_fee(tx).await
    }
}
