use crate::core::traits::sync::Async;
use crate::logger::traits::logger::BaseLogger;

pub trait HasLoggerType: Async {
    type Logger: BaseLogger;
}

pub trait HasLogger: HasLoggerType {
    fn logger(&self) -> &Self::Logger;
}
