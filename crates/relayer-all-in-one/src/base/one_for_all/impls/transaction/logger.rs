use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext> HasLoggerType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Logger = TxContext::Logger;
}

impl<TxContext> HasLogger for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn logger(&self) -> &Self::Logger {
        self.tx_context.logger()
    }
}
