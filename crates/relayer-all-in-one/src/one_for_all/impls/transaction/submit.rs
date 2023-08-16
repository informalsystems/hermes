use async_trait::async_trait;
use ibc_relayer_components::transaction::traits::submit::TxSubmitter;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> TxSubmitter<OfaTxWrapper<TxContext>> for OfaComponents
where
    TxContext: OfaTxContext,
{
    async fn submit_tx(
        context: &OfaTxWrapper<TxContext>,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::TxHash, TxContext::Error> {
        context.tx_context.submit_tx(tx).await
    }
}
