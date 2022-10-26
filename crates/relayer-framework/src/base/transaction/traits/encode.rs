use async_trait::async_trait;

use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanEncodeTx: HasTxTypes {
    async fn encode_tx_with_fee(
        &self,
        fee: Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Self::Error>;
}

#[async_trait]
pub trait TxFeeEstimator<Context>
where
    Context: HasTxTypes,
{
    async fn encode_tx_with_fee(
        context: &Context,
        fee: Context::Fee,
        messages: &[Context::Message],
    ) -> Result<Context::Transaction, Context::Error>;
}
