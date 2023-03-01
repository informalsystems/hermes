use core::cell::RefCell;
use core::fmt::{self, Debug, Display};
use tracing::{debug, error, event_enabled, info, trace, warn, Level};

use ibc_relayer_components::logger::traits::types::BaseLogger;

pub struct TracingLogger;

#[derive(Clone)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

impl Default for LogLevel {
    fn default() -> Self {
        Self::Info
    }
}

pub struct Log<'a> {
    pub fields: RefCell<Vec<(&'a str, LogValue<'a>)>>,
}

impl<'a> Log<'a> {
    pub fn new() -> Self {
        Self {
            fields: RefCell::new(Vec::new()),
        }
    }
}

pub enum LogValue<'a> {
    Display(&'a dyn Display),
    Debug(&'a dyn Debug),
}

impl<'a> Display for Log<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.fields.borrow().iter()).finish()
    }
}

impl<'a> Debug for LogValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Display(value) => Display::fmt(*value, f),
            Self::Debug(value) => Debug::fmt(*value, f),
        }
    }
}

impl BaseLogger for TracingLogger {
    type Log<'a, 'r> = Log<'a>;

    type LogValue<'a> = LogValue<'a>;

    type LogLevel = LogLevel;

    fn default_level() -> LogLevel {
        Default::default()
    }

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
