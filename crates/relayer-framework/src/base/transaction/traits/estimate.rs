use async_trait::async_trait;

use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanEstimateTxFee: HasTxTypes {
    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error>;
}

#[async_trait]
pub trait TxFeeEstimator<Context>
where
    Context: HasTxTypes,
{
    async fn estimate_tx_fee(
        context: &Context,
        tx: &Context::Transaction,
    ) -> Result<Context::Fee, Context::Error>;
}
