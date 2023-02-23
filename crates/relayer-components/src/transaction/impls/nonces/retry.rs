use core::future::Future;
use core::marker::PhantomData;
use core::pin::Pin;

use crate::core::traits::sync::Async;
use crate::std_prelude::*;
use crate::transaction::traits::nonce::{CanRefreshNonce, HasNonceMismatchError, NonceAllocator};
use crate::transaction::traits::types::HasTxTypes;

/**
   A nonce allocator that retries the nonce continuation in case there is
   a nonce mismatch error. It would call [`CanRefreshNonce::refresh_nonce`]
   to refresh the nonce, and then call the continuation again.
*/
pub struct RetryNonceAllocator<InAllocator>(pub PhantomData<InAllocator>);

pub trait HasMaxNonceRetry: Async {
    fn max_nonce_retry(&self) -> usize;
}

impl<Context, InAllocator> NonceAllocator<Context> for RetryNonceAllocator<InAllocator>
where
    Context: HasTxTypes + HasMaxNonceRetry + CanRefreshNonce + HasNonceMismatchError,
    InAllocator: NonceAllocator<Context>,
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
            + 'a,
    {
        Box::pin(async {
            let max_retry = context.max_nonce_retry();
            let mut current_retry = 0;

            loop {
                let res = InAllocator::with_allocated_nonce(context, signer, cont).await;

                match res {
                    Err(e) => {
                        if Context::try_extract_nonce_mismatch_error(&e).is_some()
                            && current_retry < max_retry
                        {
                            context.refresh_nonce(signer).await?;
                            current_retry += 1;
                            continue;
                        } else {
                            return Err(e);
                        }
                    }
                    Ok(res) => return Ok(res),
                }
            }
        })
    }
}
