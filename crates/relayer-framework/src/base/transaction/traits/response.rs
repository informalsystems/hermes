use async_trait::async_trait;

use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryTxResponse: HasTxTypes {
    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error>;
}

#[async_trait]
pub trait TxResponseQuerier<Context>
where
    Context: HasTxTypes,
{
    async fn query_tx_response(
        context: &Context,
        tx_hash: &Context::TxHash,
    ) -> Result<Option<Context::TxResponse>, Context::Error>;
}
