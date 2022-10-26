use crate::base::transaction::traits::types::{HasTxTypes, SameTxTypes};

pub trait CanBuildTxContext: HasTxTypes {
    type TxContext: SameTxTypes<Self>;

    fn build_tx_context(
        &self,
        wallet: &Self::Wallet,
        nonce: &Self::Nonce,
        memo: &Self::Memo,
    ) -> Self::TxContext;
}
