use async_trait::async_trait;

use crate::core::traits::error::InjectError;
use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

pub struct NonceMistmatchError<Nonce> {
    pub expected_nonce: Nonce,
    pub given_nonce: Nonce,
}

pub trait HasNonceMismatchError:
    HasTxTypes + InjectError<NonceMistmatchError<Self::Nonce>>
{
    fn try_extract_nonce_mismatch_error(
        e: &Self::Error,
    ) -> Option<NonceMistmatchError<Self::Nonce>>;
}

#[async_trait]
pub trait CanQueryNonce: HasTxTypes {
    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Self::Error>;
}

pub trait HasNonceGuard: HasTxTypes {
    type NonceGuard<'a>: Send + Sync;

    fn deref_nonce<'a, 'b>(guard: &'a Self::NonceGuard<'b>) -> &'a Self::Nonce;
}

#[async_trait]
pub trait CanAllocateNonce: HasTxTypes + HasNonceGuard {
    async fn allocate_nonce<'a>(
        &'a self,
        signer: &'a Self::Signer,
    ) -> Result<Self::NonceGuard<'a>, Self::Error>;
}

#[async_trait]
pub trait NonceAllocator<Context>
where
    Context: HasTxTypes + HasNonceGuard,
{
    async fn allocate_nonce<'a>(
        context: &'a Context,
        signer: &'a Context::Signer,
    ) -> Result<Context::NonceGuard<'a>, Context::Error>;
}
