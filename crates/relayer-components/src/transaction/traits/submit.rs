use async_trait::async_trait;

use crate::core::traits::component::DelegateComponent;
use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

pub struct TxSubmitterComponent;

#[async_trait]
pub trait TxSubmitter<TxContext>
where
    TxContext: HasTxTypes,
{
    async fn submit_tx(
        context: &TxContext,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::TxHash, TxContext::Error>;
}

#[async_trait]
pub trait CanSubmitTx: HasTxTypes {
    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error>;
}

#[async_trait]
impl<TxContext, Component> TxSubmitter<TxContext> for Component
where
    TxContext: HasTxTypes,
    Component: DelegateComponent<TxSubmitterComponent>,
    Component::Delegate: TxSubmitter<TxContext>,
{
    async fn submit_tx(
        context: &TxContext,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::TxHash, TxContext::Error> {
        Component::Delegate::submit_tx(context, tx).await
    }
}

#[async_trait]
impl<TxContext> CanSubmitTx for TxContext
where
    TxContext: HasTxTypes + DelegateComponent<TxSubmitterComponent>,
    TxContext::Delegate: TxSubmitter<TxContext>,
{
    async fn submit_tx(&self, tx: &Self::Transaction) -> Result<Self::TxHash, Self::Error> {
        TxContext::Delegate::submit_tx(self, tx).await
    }
}
