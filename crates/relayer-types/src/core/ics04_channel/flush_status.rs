use std::fmt::Display;
use std::fmt::Error as FmtError;
use std::fmt::Formatter;
use std::str::FromStr;

use serde::Deserialize;
use serde::Serialize;

use ibc_proto::ibc::core::channel::v1::FlushStatus as RawFlushStatus;

use crate::core::ics04_channel::error::Error;

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlushStatus {
    #[default]
    NotinflushUnspecified = 0,
    Flushing = 1,
    Flushcomplete = 2,
}

impl Display for FlushStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            FlushStatus::NotinflushUnspecified => write!(f, "FLUSH_STATUS_NOTINFLUSH_UNSPECIFIED"),
            FlushStatus::Flushing => write!(f, "FLUSH_STATUS_FLUSHING"),
            FlushStatus::Flushcomplete => write!(f, "FLUSH_STATUS_FLUSHCOMPLETE"),
        }
    }
}

impl FromStr for FlushStatus {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().trim_start_matches("flush_status_") {
            "notinflush_unspecified" => Ok(Self::NotinflushUnspecified),
            "flushing" => Ok(Self::Flushing),
            "flushcomplete" => Ok(Self::Flushcomplete),
            _ => Err(Error::unknown_flush_status_type(s.to_string())),
        }
    }
}

impl TryFrom<RawFlushStatus> for FlushStatus {
    type Error = Error;

    fn try_from(value: RawFlushStatus) -> Result<Self, Self::Error> {
        value.try_into()
    }
}

impl From<FlushStatus> for RawFlushStatus {
    fn from(value: FlushStatus) -> Self {
        match value {
            FlushStatus::NotinflushUnspecified => RawFlushStatus::NotinflushUnspecified,
            FlushStatus::Flushing => RawFlushStatus::Flushing,
            FlushStatus::Flushcomplete => RawFlushStatus::Flushcomplete,
        }
    }
}

impl TryFrom<i32> for FlushStatus {
    type Error = Error;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(FlushStatus::NotinflushUnspecified),
            1 => Ok(FlushStatus::Flushing),
            2 => Ok(FlushStatus::Flushcomplete),
            _ => Err(Error::unknown_flush_status(value)),
        }
    }
}
