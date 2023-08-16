use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::runtime::traits::mutex::HasMutex;
use crate::std_prelude::*;
use crate::transaction::traits::logs::logger::CanLogTx;
use crate::transaction::traits::logs::nonce::CanLogNonce;
use crate::transaction::traits::nonce::allocate::NonceAllocator;
use crate::transaction::traits::nonce::mutex::HasMutexForNonceAllocation;
use crate::transaction::traits::nonce::query::CanQueryNonce;

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
