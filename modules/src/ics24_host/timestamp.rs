use anomaly::{BoxError, Context};
use serde_derive::{Deserialize, Serialize};
use std::convert::TryInto;
use std::fmt::Display;
use std::num::{ParseIntError, TryFromIntError};
use std::str::FromStr;
use thiserror::Error;

use chrono::{offset::Utc, DateTime, TimeZone};

/// A newtype wrapper over `Option<DateTime<Utc>>` to keep track of
/// IBC packet timeout. In protocol buffer, the timestamp is represented
/// as a `u64` value, with 0 representing the absence of timestamp. We use
/// an explicit `Option` type to distinguish this when converting between
/// a `u64` value and a raw timestamp.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Deserialize, Serialize, Hash)]
pub struct Timestamp {
    time: Option<DateTime<Utc>>,
}

impl Timestamp {
    pub fn from_nanoseconds(nanoseconds: u64) -> Result<Timestamp, TryFromIntError> {
        if nanoseconds == 0 {
            Ok(Timestamp { time: None })
        } else {
            let nanoseconds = nanoseconds.try_into()?;
            Ok(Timestamp {
                time: Some(Utc.timestamp_nanos(nanoseconds)),
            })
        }
    }

    pub fn from_datetime(time: DateTime<Utc>) -> Timestamp {
        Timestamp { time: Some(time) }
    }

    pub fn as_nanoseconds(&self) -> u64 {
        self.time
            .map_or(0, |time| time.timestamp_nanos().try_into().unwrap())
    }

    pub fn as_datetime(&self) -> Option<DateTime<Utc>> {
        self.time
    }

    pub fn is_valid(&self) -> bool {
        self.time.is_some()
    }

    pub fn is_before_or_same_as(&self, other: &Timestamp) -> bool {
        match (self.time, other.time) {
            (Some(time1), Some(time2)) => time1 <= time2,
            _ => false,
        }
    }

    pub fn is_after(&self, other: &Timestamp) -> bool {
        match (self.time, other.time) {
            (Some(time1), Some(time2)) => time1 > time2,
            _ => false,
        }
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Timestamp({})",
            self.time
                .map_or("NoTimestamp".to_string(), |time| time.to_rfc3339())
        )
    }
}

pub type ParseTimestampError = anomaly::Error<ParseTimestampErrorKind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ParseTimestampErrorKind {
    #[error("Error parsing integer from string: {0}")]
    ParseIntError(ParseIntError),

    #[error("Error converting from u64 to i64: {0}")]
    TryFromIntError(TryFromIntError),
}

impl ParseTimestampErrorKind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}

impl FromStr for Timestamp {
    type Err = ParseTimestampError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let seconds =
            u64::from_str(s).map_err(|err| ParseTimestampErrorKind::ParseIntError(err))?;

        Ok(Timestamp::from_nanoseconds(seconds)
            .map_err(|err| ParseTimestampErrorKind::TryFromIntError(err))?)
    }
}

impl Default for Timestamp {
    fn default() -> Self {
        Timestamp { time: None }
    }
}
