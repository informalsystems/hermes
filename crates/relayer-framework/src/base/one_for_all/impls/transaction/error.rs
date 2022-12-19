use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::impls::poll::InjectNoTxResponseError;

impl<TxContext> HasErrorType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Error = TxContext::Error;
}

impl<TxContext> InjectNoTxResponseError for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn tx_no_response_error(tx_hash: &Self::TxHash) -> Self::Error {
        TxContext::tx_no_response_error(tx_hash)
    }
}
