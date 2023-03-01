use core::fmt::{Debug, Display};

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
    type Log<'a, 'r>;

    type LogValue<'a>;

    type LogLevel: Clone + Async;

    fn default_level() -> Self::LogLevel;

    fn new_log<'a>(
        &'a self,
        level: Self::LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(&'r Self::Log<'a, 'r>),
    );

    fn log_field<'a, 'b, 'r>(log: &Self::Log<'a, 'r>, key: &'b str, value: Self::LogValue<'b>)
    where
        'b: 'a;

    fn display_value<'a, T>(value: &'a T) -> Self::LogValue<'a>
    where
        T: Display;

    fn debug_value<'a, T>(value: &'a T) -> Self::LogValue<'a>
    where
        T: Debug;
}

pub struct LogWrapper<'a, 'r, Context>
where
    Context: HasLoggerType,
{
    pub log: &'r <Context::Logger as BaseLogger>::Log<'a, 'r>,
}

impl<'a, 'r, Context> LogWrapper<'a, 'r, Context>
where
    Context: HasLoggerType,
{
    pub fn field<'b>(
        &self,
        key: &'b str,
        value: <Context::Logger as BaseLogger>::LogValue<'b>,
    ) -> &Self
    where
        'b: 'a,
    {
        Context::Logger::log_field(&self.log, key, value);

        self
    }

    pub fn display<'b, T>(&self, key: &'b str, value: &'b T) -> &Self
    where
        'b: 'a,
        T: Display,
    {
        self.field(key, Context::Logger::display_value(value))
    }

    pub fn debug<'b, T>(&self, key: &'b str, value: &'b T) -> &Self
    where
        'b: 'a,
        T: Debug,
    {
        self.field(key, Context::Logger::debug_value(value))
    }

    pub fn value<'b, T>(&self, key: &'b str, value: &'b T) -> &Self
    where
        'b: 'a,
        Context: CanLogValue<T>,
    {
        self.field(key, Context::log_value(value))
    }
}

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

pub trait HasFoo {
    type Foo;

    fn foo(&self) -> &Self::Foo;
}

pub trait TestLogger {
    fn test(&self);
}

impl<Context> TestLogger for Context
where
    Context: HasLogger + HasFoo + CanLogValue<Context::Foo>,
{
    fn test(&self) {
        let foo = self.foo();
        let bar = 42;

        self.log(Context::Logger::default_level(), "testing", |log| {
            log.value("foo", foo).debug("bar", &bar);
        });
    }
}
