use async_trait::async_trait;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::transaction::impls::nonces::mutex::AllocateNonceWithMutex;
use ibc_relayer_components::transaction::traits::nonce::{
    CanAllocateNonce, CanQueryNonce, HasNonceGuard, NonceAllocator,
};

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<TxContext> CanQueryNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Self::Error> {
        self.tx_context.query_nonce(signer).await
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

#[async_trait]
impl<TxContext> CanAllocateNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    async fn allocate_nonce<'a>(
        &'a self,
        signer: &'a Self::Signer,
    ) -> Result<Self::NonceGuard<'a>, Self::Error> {
        AllocateNonceWithMutex::allocate_nonce(self, signer).await
    }
}
