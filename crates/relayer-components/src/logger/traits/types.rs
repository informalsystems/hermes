use core::fmt::Display;

use alloc::string::ToString;

use crate::core::traits::sync::Async;

pub trait HasLoggerType: Async {
    type Logger: BaseLogger;
}

pub trait HasLogger: HasLoggerType {
    fn logger(&self) -> &Self::Logger;
}

pub trait BaseLogger: Async {
    type Log<'r>: Async;

    type LogLevel: Default + Async;

    type LogValue<'a>: Async;

    fn new_log(
        &self,
        level: Self::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(Self::Log<'r>),
    );

    fn log_field<'a, 'r>(log: &Self::Log<'r>, key: &str, value: Self::LogValue<'a>);

    fn display_value<'a, T>(value: T) -> Self::LogValue<'a>
    where
        T: Display + ?Sized + 'a;
}

pub struct LogWrapper<'r, Logger>
where
    Logger: BaseLogger,
{
    pub log: Logger::Log<'r>,
}

impl<'r, Logger> LogWrapper<'r, Logger>
where
    Logger: BaseLogger,
{
    pub fn field<'a>(&self, key: &str, value: Logger::LogValue<'a>) -> &Self {
        Logger::log_field(&self.log, key, value);

        self
    }

    pub fn display<T>(&self, key: &str, value: T) -> &Self
    where
        T: Display,
    {
        Logger::log_field(&self.log, key, Logger::display_value(value));

        self
    }

    pub fn done(&self) {}
}

pub trait SimpleLogger: BaseLogger {
    fn log(
        &self,
        level: Self::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'r, Self>),
    );
}

impl<Logger> SimpleLogger for Logger
where
    Logger: BaseLogger,
{
    fn log(
        &self,
        level: Self::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'r, Self>),
    ) {
        Logger::new_log(&self, level, message, |log| {
            build_log(LogWrapper { log });
        });
    }
}

pub trait TestLogger {
    fn test(&self);
}

impl<Context, Logger> TestLogger for Context
where
    Context: HasLogger<Logger = Logger>,
    Logger: BaseLogger,
{
    fn test(&self) {
        let logger = self.logger();

        let foo = "foo".to_string();
        let bar = 42;

        logger.log(Default::default(), "testing", |log| {
            log.display("foo", &foo)
                .display("bar", format_args!("{:?}", bar))
                .done()
        });
    }
}
