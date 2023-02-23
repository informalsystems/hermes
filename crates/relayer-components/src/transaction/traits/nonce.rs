use core::future::Future;
use core::pin::Pin;

use async_trait::async_trait;

use crate::core::traits::error::InjectError;
use crate::core::traits::sync::Async;
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

/**
   Allow a cached nonce to be refresh in the event that transaction submission
   experience nonce mismatch error.

   To ensure that the nonce is refreshed correctly, the context MUST wait for
   ALL pending transactions to return before returning from this call.
   Otherwise there would be race condition that cause the refreshed nonce to be
   invalidated if any transaction is committed at the same time.

   The context MUST also make sure that multiple parallel calls to `refresh_nonce`
   are aggregated so that it is refreshed only once. There should also be some
   back off mechanism to wait for a while after all pending transactions are
   cleared, so that to avoid the `refresh_nonce` being called again immediately.
*/
#[async_trait]
pub trait CanRefreshNonce: HasTxTypes {
    async fn refresh_nonce(&self, signer: &Self::Signer) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait NonceRefresher<Context>
where
    Context: HasTxTypes,
{
    async fn refresh_nonce(
        context: &Context,
        signer: &Context::Signer,
    ) -> Result<(), Context::Error>;
}

#[async_trait]
pub trait CanIncrementNonce: HasTxTypes {
    fn increment_nonce(nonce: &Self::Nonce) -> Self::Nonce;
}

pub trait CanAllocateNonce: HasTxTypes {
    fn with_allocated_nonce<'a, R, Cont>(
        &'a self,
        signer: &'a Self::Signer,
        cont: &'a Cont,
    ) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
    where
        R: Async,
        Cont: Fn(Self::Nonce) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
            + Send
            + Sync
            + 'a;
}

pub trait NonceAllocator<Context>
where
    Context: HasTxTypes,
{
    fn with_allocated_nonce<'a, R, Cont>(
        context: &'a Context,
        signer: &'a Context::Signer,
        cont: &'a Cont,
    ) -> Pin<Box<dyn Future<Output = Result<R, Context::Error>> + Send + 'a>>
    where
        R: Async + 'a,
        Cont: Fn(
                Context::Nonce,
            ) -> Pin<Box<dyn Future<Output = Result<R, Context::Error>> + Send + 'a>>
            + Send
            + Sync
            + 'a;
}
