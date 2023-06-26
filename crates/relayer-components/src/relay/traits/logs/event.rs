use crate::chain::traits::logs::event::CanLogChainEvent;
use crate::chain::traits::types::event::HasEventType;
use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;

pub trait CanLogRelayEvent: HasRelayChains + HasLoggerType {
    fn log_src_event<'a>(
        event: &'a <Self::SrcChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn log_dst_event<'a>(
        event: &'a <Self::DstChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}

impl<Relay, Logger> CanLogRelayEvent for Relay
where
    Logger: BaseLogger,
    Relay: HasRelayChains + HasLoggerType<Logger = Logger>,
    Relay::SrcChain: CanLogChainEvent<Logger = Logger>,
    Relay::DstChain: CanLogChainEvent<Logger = Logger>,
{
    fn log_src_event<'a>(
        event: &'a <Self::SrcChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        Self::SrcChain::log_event(event)
    }

    fn log_dst_event<'a>(
        event: &'a <Self::DstChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        Self::DstChain::log_event(event)
    }
}

pub trait CanLogTargetEvent<Target>: HasRelayChains + HasLoggerType
where
    Target: ChainTarget<Self>,
{
    fn log_target_event<'a>(
        event: &'a <Target::TargetChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}

impl<Relay, Target, Logger> CanLogTargetEvent<Target> for Relay
where
    Logger: BaseLogger,
    Relay: HasRelayChains + HasLoggerType<Logger = Logger>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: CanLogChainEvent<Logger = Logger>,
{
    fn log_target_event<'a>(
        event: &'a <Target::TargetChain as HasEventType>::Event,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        Target::TargetChain::log_event(event)
    }
}
