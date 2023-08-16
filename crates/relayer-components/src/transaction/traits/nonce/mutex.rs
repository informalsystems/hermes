use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::runtime::HasRuntime;
use crate::transaction::traits::nonce::guard::HasNonceGuard;
use crate::transaction::traits::types::HasSignerType;

/**
   A naive nonce allocator that simply query the current nonce from the context
   and then pass it to the continuation.

   To ensure that the nonce works safely with parallel transaction submissions,
   the allocator requires the context to provide a mutex, which is acquired across
   the time when the nonce is being allocated and used. Because of this, the naive
   allocator only allows one transaction to be submitted at a time.
*/
pub trait HasMutexForNonceAllocation: HasRuntime + HasNonceGuard + HasSignerType
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
