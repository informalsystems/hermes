use crate::logger::traits::has_logger::{HasLogger, HasLoggerType};
use crate::logger::traits::logger::BaseLogger;
use crate::logger::traits::wrapper::LogWrapper;

pub trait SimpleLogger: HasLoggerType {
    fn log<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self>),
    );

    fn log_message(&self, level: <Self::Logger as BaseLogger>::LogLevel, message: &str);
}

impl<Context, Logger> SimpleLogger for Context
where
    Context: HasLogger<Logger = Logger>,
    Logger: BaseLogger,
{
    fn log<'a>(
        &'a self,
        level: Logger::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self>),
    ) {
        self.logger().new_log(level, message, |log| {
            build_log(LogWrapper { log });
        });
    }

    fn log_message(&self, level: <Self::Logger as BaseLogger>::LogLevel, message: &str) {
        self.log(level, message, |_| {})
    }
}
