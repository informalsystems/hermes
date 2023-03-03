use core::future::Future;
use core::pin::Pin;

use crate::core::traits::sync::Async;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;
use crate::transaction::traits::logs::logger::CanLogTx;
use crate::transaction::traits::logs::nonce::CanLogNonce;
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
    Context: CanLogTx + CanLogNonce + CanQueryNonce + HasMutexForNonceAllocation,
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
            context.log_tx(
                Context::Logger::LEVEL_TRACE,
                "acquiring nonce mutex",
                |_| {},
            );

            let mutex = context.mutex_for_nonce_allocation(signer);

            let _guard = Context::Runtime::acquire_mutex(mutex).await;

            context.log_tx(Context::Logger::LEVEL_TRACE, "acquired nonce mutex", |_| {});

            let nonce = context.query_nonce(signer).await?;

            context.log_tx(Context::Logger::LEVEL_TRACE, "assigned nonce", |log| {
                log.field("nonce", Context::log_nonce(&nonce));
            });

            let res = cont(nonce).await;

            context.log_tx(
                Context::Logger::LEVEL_TRACE,
                "releasing nonce mutex",
                |_| {},
            );

            Ok(res?)
        })
    }
}
