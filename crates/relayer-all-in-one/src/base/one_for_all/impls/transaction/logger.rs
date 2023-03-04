use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::logger::traits::logger::BaseLogger;
use ibc_relayer_components::transaction::traits::logs::nonce::CanLogNonce;

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

impl<TxContext> CanLogNonce for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn log_nonce<'a>(nonce: &'a Self::Nonce) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        TxContext::log_nonce(nonce)
    }
}
