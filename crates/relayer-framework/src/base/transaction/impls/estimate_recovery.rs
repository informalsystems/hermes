use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::transaction::traits::estimate::TxFeeEstimator;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub trait CanRecoverEstimateError: HasTxTypes {
    fn try_recover_estimate_error(&self, e: Self::Error) -> Result<Self::Fee, Self::Error>;
}

pub struct TryRecoverEstimateError<InEstimator>(pub PhantomData<InEstimator>);

#[async_trait]
impl<Context, InEstimator> TxFeeEstimator<Context> for TryRecoverEstimateError<InEstimator>
where
    Context: CanRecoverEstimateError,
    InEstimator: TxFeeEstimator<Context>,
{
    async fn estimate_tx_fee(
        context: &Context,
        tx: &Context::Transaction,
    ) -> Result<Context::Fee, Context::Error> {
        let res = InEstimator::estimate_tx_fee(context, tx).await;

        match res {
            Ok(fee) => Ok(fee),
            Err(e) => context.try_recover_estimate_error(e),
        }
    }
}
