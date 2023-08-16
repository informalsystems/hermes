use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;
use crate::transaction::traits::logs::logger::CanLogTx;
use crate::transaction::traits::logs::nonce::CanLogNonce;
use crate::transaction::traits::nonce::{CanQueryNonce, HasNonceGuard, NonceAllocator};

/**
   A naive nonce allocator that simply query the current nonce from the context
   and then pass it to the continuation.

   To ensure that the nonce works safely with parallel transaction submissions,
   the allocator requires the context to provide a mutex, which is acquired across
   the time when the nonce is being allocated and used. Because of this, the naive
   allocator only allows one transaction to be submitted at a time.
*/
pub trait HasMutexForNonceAllocation: HasRuntime + HasNonceGuard
where
    Self::Runtime: HasMutex,
{
    fn mutex_for_nonce_allocation(
        &self,
        signer: &Self::Signer,
    ) -> &<Self::Runtime as HasMutex>::Mutex<()>;

    fn mutex_to_nonce_guard<'a>(
        mutex_guard: <Self::Runtime as HasMutex>::MutexGuard<'a, ()>,
        nonce: Self::Nonce,
    ) -> Self::NonceGuard<'a>;
}

pub struct AllocateNonceWithMutex;

#[async_trait]
impl<Context> NonceAllocator<Context> for AllocateNonceWithMutex
where
    Context: CanLogTx + CanLogNonce + CanQueryNonce + HasMutexForNonceAllocation,
    Context::Runtime: HasMutex,
{
    async fn allocate_nonce<'a>(
        context: &'a Context,
        signer: &'a Context::Signer,
    ) -> Result<Context::NonceGuard<'a>, Context::Error> {
        context.log_tx(
            Context::Logger::LEVEL_TRACE,
            "acquiring nonce mutex",
            |_| {},
        );

        let mutex = context.mutex_for_nonce_allocation(signer);

        let mutex_guard = Context::Runtime::acquire_mutex(mutex).await;

        context.log_tx(Context::Logger::LEVEL_TRACE, "acquired nonce mutex", |_| {});

        let nonce = context.query_nonce(signer).await?;

        context.log_tx(Context::Logger::LEVEL_TRACE, "assigned nonce", |log| {
            log.field("nonce", Context::log_nonce(&nonce));
        });

        let nonce_guard = Context::mutex_to_nonce_guard(mutex_guard, nonce);

        Ok(nonce_guard)
    }
}
