use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::runtime::traits::runtime::HasRuntime;

impl<TxContext> HasRuntime for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Runtime = OfaRuntimeWrapper<TxContext::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.tx_context.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error {
        TxContext::runtime_error(e)
    }
}
