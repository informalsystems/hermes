use core::future::Future;
use core::pin::Pin;

use crate::core::traits::sync::Async;
use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;
use crate::transaction::traits::nonce::{CanQueryNonce, NonceAllocator};
use crate::transaction::traits::types::HasTxTypes;

/**!
   A naive nonce allocator that simply query the current nonce from the context
   and then pass it to the continuation.

   To ensure that the nonce works safely with parallel transaction submissions,
   the allocator requires the context to provide a mutex, which is acquired across
   the time when the nonce is being allocated and used. Because of this, the naive
   allocator only allows one transaction to be submitted at a time.
*/

pub trait HasMutexForNonceAllocation: HasRuntime + HasTxTypes
where
    Self::Runtime: HasMutex,
{
    fn mutex_for_nonce_allocation(
        &self,
        signer: &Self::Signer,
    ) -> &<Self::Runtime as HasMutex>::Mutex<()>;
}

pub struct NaiveNonceAllocator;

impl<Context> NonceAllocator<Context> for NaiveNonceAllocator
where
    Context: CanQueryNonce + HasMutexForNonceAllocation,
    Context::Runtime: HasMutex,
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
        Box::pin(async move {
            let mutex = context.mutex_for_nonce_allocation(signer);

            let _guard = Context::Runtime::acquire_mutex(mutex).await;

            let nonce = context.query_nonce(signer).await?;

            let res = cont(nonce).await?;

            Ok(res)
        })
    }
}
