use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::response::query::CanQueryTxResponse;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> CanQueryTxResponse for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error> {
        self.tx_context.query_tx_response(tx_hash).await
    }
}
