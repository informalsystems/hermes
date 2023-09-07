use async_trait::async_trait;

use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

pub struct TxResponseQuerierComponent;

#[async_trait]
pub trait TxResponseQuerier<TxContext>
where
    TxContext: HasTxTypes,
{
    async fn query_tx_response(
        context: &TxContext,
        tx_hash: &TxContext::TxHash,
    ) -> Result<Option<TxContext::TxResponse>, TxContext::Error>;
}

#[async_trait]
pub trait CanQueryTxResponse: HasTxTypes {
    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error>;
}

#[async_trait]
impl<TxContext, Component> TxResponseQuerier<TxContext> for Component
where
    TxContext: HasTxTypes,
    Component: DelegateComponent<TxResponseQuerierComponent>,
    Component::Delegate: TxResponseQuerier<TxContext>,
{
    async fn query_tx_response(
        context: &TxContext,
        tx_hash: &TxContext::TxHash,
    ) -> Result<Option<TxContext::TxResponse>, TxContext::Error> {
        Component::Delegate::query_tx_response(context, tx_hash).await
    }
}

#[async_trait]
impl<TxContext> CanQueryTxResponse for TxContext
where
    TxContext: HasTxTypes + HasComponents,
    TxContext::Components: TxResponseQuerier<TxContext>,
{
    async fn query_tx_response(
        &self,
        tx_hash: &Self::TxHash,
    ) -> Result<Option<Self::TxResponse>, Self::Error> {
        TxContext::Components::query_tx_response(self, tx_hash).await
    }
}
