use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::estimate::TxFeeEstimator;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> TxFeeEstimator<OfaTxWrapper<TxContext>> for OfaComponents
where
    TxContext: OfaTxContext,
{
    async fn estimate_tx_fee(
        context: &OfaTxWrapper<TxContext>,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::Fee, TxContext::Error> {
        context.tx_context.estimate_tx_fee(tx).await
    }
}
