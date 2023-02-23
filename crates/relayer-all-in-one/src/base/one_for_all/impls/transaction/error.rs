use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::transaction::impls::poll::InjectNoTxResponseError;

use crate::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use crate::one_for_all::types::transaction::OfaTxWrapper;

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
