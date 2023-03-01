use crate::chain::traits::logs::event::CanLogChainEvent;
use crate::chain::traits::types::event::HasEventType;
use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;
use crate::relay::traits::types::HasRelayTypes;

pub trait CanLogRelayEvent: HasRelayTypes + HasLoggerType {
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
    Relay: HasRelayTypes + HasLoggerType<Logger = Logger>,
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
