use crate::core::traits::error::InjectError;
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
