use async_trait::async_trait;

use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

#[async_trait]
pub trait CanSubmitTx: HasTxTypes {
    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error>;
}

#[async_trait]
pub trait TxSubmitter<Context>
where
    Context: HasTxTypes,
{
    async fn submit_tx(
        context: &Context,
        tx: &Context::Transaction,
    ) -> Result<Context::TxHash, Context::Error>;
}
