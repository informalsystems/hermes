use core::fmt::{Debug, Display};

use crate::core::traits::sync::Async;

pub trait BaseLogger: Async {
    type Log<'a, 'r>;

    type LogValue<'a>;

    type LogLevel: Default + Clone + Async;

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
