use async_trait::async_trait;

use crate::core::traits::component::DelegateComponent;
use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

pub struct TxFeeEstimatorComponent;

#[async_trait]
pub trait TxFeeEstimator<TxContext>
where
    TxContext: HasTxTypes,
{
    async fn estimate_tx_fee(
        context: &TxContext,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::Fee, TxContext::Error>;
}

#[async_trait]
pub trait CanEstimateTxFee: HasTxTypes {
    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error>;
}

#[async_trait]
impl<TxContext, Component> TxFeeEstimator<TxContext> for Component
where
    TxContext: HasTxTypes,
    Component: DelegateComponent<TxFeeEstimatorComponent>,
    Component::Delegate: TxFeeEstimator<TxContext>,
{
    async fn estimate_tx_fee(
        context: &TxContext,
        tx: &TxContext::Transaction,
    ) -> Result<TxContext::Fee, TxContext::Error> {
        Component::Delegate::estimate_tx_fee(context, tx).await
    }
}

#[async_trait]
impl<TxContext> CanEstimateTxFee for TxContext
where
    TxContext: HasTxTypes + DelegateComponent<TxFeeEstimatorComponent>,
    TxContext::Delegate: TxFeeEstimator<TxContext>,
{
    async fn estimate_tx_fee(&self, tx: &Self::Transaction) -> Result<Self::Fee, Self::Error> {
        TxContext::Delegate::estimate_tx_fee(self, tx).await
    }
}
