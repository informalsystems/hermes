use async_trait::async_trait;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::impls::poll::PollTxResponse;
use crate::base::transaction::traits::response::{
    CanPollTxResponse, CanQueryTxResponse, TxResponsePoller,
};
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

#[async_trait]
impl<TxContext> CanPollTxResponse for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn poll_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Self::TxResponse, Self::Error> {
        PollTxResponse::poll_tx_response(self, tx_hash).await
    }
}
