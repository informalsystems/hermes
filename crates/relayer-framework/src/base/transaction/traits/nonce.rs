use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;

use crate::base::core::traits::error::InjectError;
use crate::base::core::traits::sync::Async;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

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

#[async_trait]
pub trait CanIncrementNonce: HasTxTypes {
    fn increment_nonce(nonce: &Self::Nonce) -> Self::Nonce;
}

pub trait CanAllocateNonce: HasTxTypes {
    fn with_allocated_nonce<'a, R, Cont>(
        &'a self,
        signer: &'a Self::Signer,
        cont: Cont,
    ) -> Pin<Box<dyn Future<Output = Result<R, Self::Error>> + Send + 'a>>
    where
        R: Async + 'a,
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
        cont: Cont,
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
