use async_trait::async_trait;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::transaction::traits::nonce::guard::HasNonceGuard;
use ibc_relayer_components::transaction::traits::nonce::query::NonceQuerier;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> NonceQuerier<OfaTxWrapper<TxContext>> for OfaComponents
where
    TxContext: OfaTxContext,
{
    async fn query_nonce(
        context: &OfaTxWrapper<TxContext>,
        signer: &TxContext::Signer,
    ) -> Result<TxContext::Nonce, TxContext::Error> {
        context.tx_context.query_nonce(signer).await
    }
}

#[async_trait]
impl<TxContext> HasNonceGuard for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type NonceGuard<'a> = (
        <TxContext::Runtime as HasMutex>::MutexGuard<'a, ()>,
        TxContext::Nonce,
    );

    fn deref_nonce<'a, 'b>((_, nonce): &'a Self::NonceGuard<'b>) -> &'a Self::Nonce {
        &nonce
    }
}
