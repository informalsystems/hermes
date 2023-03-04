use core::fmt::{Debug, Display};

use crate::logger::traits::logger::BaseLogger;

pub struct LogWrapper<'a, 'r, Logger>
where
    Logger: BaseLogger,
{
    pub log: &'r Logger::Log<'a, 'r>,
}

impl<'a, 'r, Logger> LogWrapper<'a, 'r, Logger>
where
    Logger: BaseLogger,
{
    pub fn field<'b>(&self, key: &'b str, value: Logger::LogValue<'b>) -> &Self
    where
        'b: 'a,
    {
        Logger::log_field(self.log, key, value);

        self
    }

    pub fn display<'b, T>(&self, key: &'b str, value: &'b T) -> &Self
    where
        'b: 'a,
        T: Display,
    {
        self.field(key, Logger::display_value(value))
    }

    pub fn debug<'b, T>(&self, key: &'b str, value: &'b T) -> &Self
    where
        'b: 'a,
        T: Debug,
    {
        self.field(key, Logger::debug_value(value))
    }

    pub fn nested<'b>(
        &self,
        key: &'b str,
        build_log: impl for<'s> FnOnce(LogWrapper<'b, 's, Logger>),
    ) where
        'b: 'a,
    {
        let value = Logger::map_values(|log| {
            build_log(LogWrapper { log });
        });
        Logger::log_field(self.log, key, value);
    }
}
