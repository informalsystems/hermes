use core::fmt::{Debug, Display};
use ibc_relayer_components::logger::traits::level::{
    HasLogLevel, LevelDebug, LevelError, LevelInfo, LevelTrace, LevelWarn,
};
use ibc_relayer_components::logger::traits::logger::BaseLogger;
use tracing::{debug, error, event_enabled, info, trace, warn, Level};

use crate::tokio::logger::level::LogLevel;
use crate::tokio::logger::log::Log;
use crate::tokio::logger::value::LogValue;

pub struct TracingLogger;

impl BaseLogger for TracingLogger {
    type Log<'a, 'r> = Log<'a>;

    type LogValue<'a> = LogValue<'a>;

    type LogLevel = LogLevel;

    fn new_log<'a>(
        &'a self,
        level: LogLevel,
        message: &str,
        build_log: impl for<'r> FnOnce(&'r Self::Log<'a, 'r>),
    ) {
        match level {
            LogLevel::Trace => {
                if event_enabled!(Level::TRACE) {
                    let log = Log::new();
                    build_log(&log);
                    trace!(message = message, details = log.to_string())
                }
            }
            LogLevel::Debug => {
                if event_enabled!(Level::DEBUG) {
                    let log = Log::new();
                    build_log(&log);
                    debug!(message = message, details = log.to_string())
                }
            }
            LogLevel::Info => {
                if event_enabled!(Level::INFO) {
                    let log = Log::new();
                    build_log(&log);
                    info!(message = message, details = log.to_string())
                }
            }
            LogLevel::Warn => {
                if event_enabled!(Level::WARN) {
                    let log = Log::new();
                    build_log(&log);
                    warn!(warning = message, details = log.to_string())
                }
            }
            LogLevel::Error => {
                if event_enabled!(Level::ERROR) {
                    let log = Log::new();
                    build_log(&log);
                    error!(message = message, details = log.to_string())
                }
            }
        }
    }

    fn log_field<'a, 'b, 'r>(log: &Log<'a>, key: &'b str, value: LogValue<'a>)
    where
        'b: 'a,
    {
        log.fields.borrow_mut().push((key, value))
    }

    fn display_value<'a, T>(value: &'a T) -> LogValue<'a>
    where
        T: Display,
    {
        LogValue::Display(value)
    }

    fn debug_value<'a, T>(value: &'a T) -> LogValue<'a>
    where
        T: Debug,
    {
        LogValue::Debug(value)
    }
}

impl HasLogLevel<LevelTrace> for TracingLogger {
    const LEVEL: LogLevel = LogLevel::Trace;
}

impl HasLogLevel<LevelDebug> for TracingLogger {
    const LEVEL: LogLevel = LogLevel::Debug;
}

impl HasLogLevel<LevelInfo> for TracingLogger {
    const LEVEL: LogLevel = LogLevel::Info;
}

impl HasLogLevel<LevelWarn> for TracingLogger {
    const LEVEL: LogLevel = LogLevel::Warn;
}

impl HasLogLevel<LevelError> for TracingLogger {
    const LEVEL: LogLevel = LogLevel::Error;
}
