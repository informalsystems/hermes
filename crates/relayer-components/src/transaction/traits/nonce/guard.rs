use crate::transaction::traits::types::HasNonceType;

pub trait HasNonceGuard: HasNonceType {
    type NonceGuard<'a>: Send + Sync;

    fn deref_nonce<'a, 'b>(guard: &'a Self::NonceGuard<'b>) -> &'a Self::Nonce;
}
