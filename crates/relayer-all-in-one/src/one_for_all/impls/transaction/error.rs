use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::transaction::components::poll::InjectNoTxResponseError;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext> HasErrorType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
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
