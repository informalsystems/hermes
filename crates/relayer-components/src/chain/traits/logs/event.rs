use crate::chain::traits::types::event::HasEventType;
use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;

pub trait CanLogChainEvent: HasEventType + HasLoggerType {
    fn log_event<'a>(event: &'a Self::Event) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}
