use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::response::query::TxResponseQuerier;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> TxResponseQuerier<OfaTxWrapper<TxContext>> for OfaComponents
where
    TxContext: OfaTxContext,
{
    async fn query_tx_response(
        context: &OfaTxWrapper<TxContext>,
        tx_hash: &TxContext::TxHash,
    ) -> Result<Option<TxContext::TxResponse>, TxContext::Error> {
        context.tx_context.query_tx_response(tx_hash).await
    }
}
