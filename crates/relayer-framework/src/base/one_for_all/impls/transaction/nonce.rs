use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::impls::nonces::naive::NaiveNonceAllocator;
use crate::base::transaction::traits::nonce::{CanAllocateNonce, CanQueryNonce, NonceAllocator};
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
impl<TxContext> CanAllocateNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn with_allocated_nonce<'a, R, Cont>(
        &'a self,
        signer: &'a Self::Signer,
        cont: &'a Cont,
    ) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
    where
        R: Async + 'a,
        Cont: Fn(Self::Nonce) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
            + Send
            + Sync
            + 'a,
    {
        NaiveNonceAllocator::with_allocated_nonce(self, signer, cont)
    }
}
