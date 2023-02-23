use crate::base::transaction::traits::types::HasTxTypes;

pub trait HasFeeForSimulation: HasTxTypes {
    fn fee_for_simulation(&self) -> &Self::Fee;
}
