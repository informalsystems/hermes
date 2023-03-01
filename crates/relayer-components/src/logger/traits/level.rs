use crate::logger::traits::logger::BaseLogger;

pub struct LevelTrace;

pub struct LevelDebug;

pub struct LevelInfo;

pub struct LevelWarn;

pub struct LevelError;

pub trait HasLogLevel<Level>: BaseLogger {
    const LEVEL: Self::LogLevel;
}

pub trait HasBaseLogLevels:
    HasLogLevel<LevelTrace>
    + HasLogLevel<LevelDebug>
    + HasLogLevel<LevelInfo>
    + HasLogLevel<LevelWarn>
    + HasLogLevel<LevelError>
{
    const LEVEL_TRACE: Self::LogLevel;

    const LEVEL_DEBUG: Self::LogLevel;

    const LEVEL_INFO: Self::LogLevel;

    const LEVEL_WARN: Self::LogLevel;

    const LEVEL_ERROR: Self::LogLevel;
}

impl<Logger> HasBaseLogLevels for Logger
where
    Logger: HasLogLevel<LevelTrace>
        + HasLogLevel<LevelDebug>
        + HasLogLevel<LevelInfo>
        + HasLogLevel<LevelWarn>
        + HasLogLevel<LevelError>,
{
    const LEVEL_TRACE: Self::LogLevel = <Logger as HasLogLevel<LevelTrace>>::LEVEL;

    const LEVEL_DEBUG: Self::LogLevel = <Logger as HasLogLevel<LevelDebug>>::LEVEL;

    const LEVEL_INFO: Self::LogLevel = <Logger as HasLogLevel<LevelInfo>>::LEVEL;

    const LEVEL_WARN: Self::LogLevel = <Logger as HasLogLevel<LevelWarn>>::LEVEL;

    const LEVEL_ERROR: Self::LogLevel = <Logger as HasLogLevel<LevelError>>::LEVEL;
}
