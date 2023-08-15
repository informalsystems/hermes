use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext> HasRuntime for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Runtime = TxContext::Runtime;

    fn runtime(&self) -> &Self::Runtime {
        self.tx_context.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error {
        TxContext::runtime_error(e)
    }
}
