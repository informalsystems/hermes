use crate::chain::traits::types::chain_id::HasChainId;
use crate::logger::traits::level::HasLoggerWithBaseLevels;
use crate::logger::traits::log::CanLog;
use crate::logger::traits::logger::BaseLogger;
use crate::logger::types::wrapper::LogWrapper;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;

pub trait CanLogRelay: HasLoggerWithBaseLevels {
    fn log_relay<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    );
}

impl<Relay> CanLogRelay for Relay
where
    Relay: CanLog + HasRelayTypes,
    Relay::SrcChain: HasChainId,
    Relay::DstChain: HasChainId,
{
    fn log_relay<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    ) {
        self.log(level, message, |log| {
            log.nested("relay_context", |log| {
                log.display("src_chain_id", self.source_chain().chain_id());
                log.display("dst_chain_id", self.destination_chain().chain_id());
                log.display("src_client_id", self.source_client_id());
                log.display("dst_client_id", self.destination_client_id());
            });

            build_log(log);
        })
    }
}

pub trait CanLogRelayTarget<Target>: HasRelayTypes + HasLoggerWithBaseLevels
where
    Target: ChainTarget<Self>,
{
    fn log_relay_target<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    );
}

impl<Relay, Target> CanLogRelayTarget<Target> for Relay
where
    Relay: CanLog + HasRelayTypes,
    Target::TargetChain: HasChainId,
    Target::CounterpartyChain: HasChainId,
    Target: ChainTarget<Relay>,
{
    fn log_relay_target<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self::Logger>),
    ) {
        self.log(level, message, |log| {
            log.nested("relay_context", |log| {
                log.display("target_chain_id", Target::target_chain(self).chain_id());
                log.display(
                    "counterparty_chain_id",
                    Target::counterparty_chain(self).chain_id(),
                );
                log.display("target_client_id", Target::target_client_id(self));
                log.display(
                    "counterparty_client_id",
                    Target::counterparty_client_id(self),
                );
            });

            build_log(log);
        })
    }
}
