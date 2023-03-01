use core::fmt::{Debug, Display};

use alloc::string::ToString;

use crate::core::traits::sync::Async;

pub trait HasLoggerType: Async {
    type Logger: BaseLogger;
}

pub trait HasLogger: HasLoggerType {
    fn logger(&self) -> &Self::Logger;
}

pub trait CanLogValue<T>: HasLoggerType {
    fn log_value<'a>(value: &'a T) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}

pub trait BaseLogger: Async {
    type Log<'a, 'r>: Async;

    type LogLevel: Default + Async;

    type LogValue<'a>: Async;

    fn new_log<'a>(
        &'a self,
        level: Self::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(Self::Log<'a, 'r>),
    );

    fn log_field<'a, 'b, 'r>(log: &Self::Log<'a, 'r>, key: &str, value: Self::LogValue<'b>)
    where
        'b: 'a;

    fn display_value<'a, T>(value: T) -> Self::LogValue<'a>
    where
        T: Display + ?Sized;
}

pub struct LogWrapper<'a, 'r, Context>
where
    Context: HasLoggerType,
{
    pub log: <Context::Logger as BaseLogger>::Log<'a, 'r>,
}

impl<'a, 'r, Context> LogWrapper<'a, 'r, Context>
where
    Context: HasLoggerType,
{
    pub fn field<'b>(
        &self,
        key: &str,
        value: <Context::Logger as BaseLogger>::LogValue<'b>,
    ) -> &Self
    where
        'b: 'a,
    {
        Context::Logger::log_field(&self.log, key, value);

        self
    }

    pub fn display<T>(&self, key: &str, value: T) -> &Self
    where
        T: Display,
    {
        self.field(key, Context::Logger::display_value(value))
    }

    pub fn debug<T>(&self, key: &str, value: T) -> &Self
    where
        T: Debug,
    {
        self.display(key, format_args!("{:?}", value))
    }
}

pub trait SimpleLogger: HasLoggerType {
    fn log<'a>(
        &'a self,
        level: <Self::Logger as BaseLogger>::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(LogWrapper<'a, 'r, Self>),
    );
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
}

pub trait TestLogger {
    fn test(&self);
}

impl<Context> TestLogger for Context
where
    Context: HasLogger,
{
    fn test(&self) {
        let foo = "foo".to_string();
        let bar = 42;

        self.log(Default::default(), "testing", |log| {
            log.display("foo", &foo).debug("bar", bar);
        });
    }
}
