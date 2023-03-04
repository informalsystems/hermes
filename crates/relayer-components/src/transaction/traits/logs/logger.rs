use crate::chain::traits::types::chain_id::HasChainId;
use crate::logger::traits::level::HasLoggerWithBaseLevels;
use crate::logger::traits::log::CanLog;
use crate::logger::traits::logger::BaseLogger;
use crate::logger::types::wrapper::LogWrapper;

pub trait CanLogTx: HasLoggerWithBaseLevels {
    fn log_tx<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    );
}

impl<TxContext> CanLogTx for TxContext
where
    TxContext: CanLog + HasChainId,
{
    fn log_tx<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    ) {
        self.log(level, message, |log| {
            log.nested("tx_context", |log| {
                log.display("chain_id", self.chain_id());
            });

            build_log(log);
        })
    }
}
