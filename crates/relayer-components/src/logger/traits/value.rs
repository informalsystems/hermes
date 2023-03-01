use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;

pub trait CanLogValue<T>: HasLoggerType {
    fn log_value<'a>(value: &'a T) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}
