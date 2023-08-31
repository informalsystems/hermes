use crate::transaction::traits::types::HasSignerType;

/**
   A simplified accessor for a transaction context to provide
   one or more signers for signing transactions.

   The context may return different signers across different calls,
   so that the transaction sender can use multiple signers to
   submit parallel transactions.

   Note that this method does not support fair allocation of
   multiple signers, as the context cannot know how long a
   signer is going to be used. If we want to use a more
   sophisticated strategy to multiple signers, we can define
   more complex trait similar to
   [`NonceAllocator`](crate::transaction::traits::nonce::NonceAllocator)
   so that the usage of each signer is tracked across the implementation.

   On the other hand, this trait is suited for use in the minimal relayer,
   where there is no need to implement the logic to support parallel
   transactions or multiple signers.
*/
pub trait HasSigner: HasSignerType {
    fn get_signer(&self) -> &Self::Signer;
}
