use crate::base::transaction::traits::types::HasTxTypes;

pub trait HasMaxFee: HasTxTypes {
    fn max_fee(&self) -> &Self::Fee;
}
