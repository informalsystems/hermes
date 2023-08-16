use async_trait::async_trait;

use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;
use crate::transaction::traits::nonce::guard::HasNonceGuard;
use crate::transaction::traits::types::HasSignerType;

#[async_trait]
pub trait CanAllocateNonce: HasNonceGuard + HasSignerType + HasErrorType {
    async fn allocate_nonce<'a>(
        &'a self,
        signer: &'a Self::Signer,
    ) -> Result<Self::NonceGuard<'a>, Self::Error>;
}

#[async_trait]
pub trait NonceAllocator<TxContext>
where
    TxContext: HasNonceGuard + HasSignerType + HasErrorType,
{
    async fn allocate_nonce<'a>(
        context: &'a TxContext,
        signer: &'a TxContext::Signer,
    ) -> Result<TxContext::NonceGuard<'a>, TxContext::Error>;
}
