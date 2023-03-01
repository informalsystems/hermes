use core::fmt::{Debug, Display};

use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;

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
}
