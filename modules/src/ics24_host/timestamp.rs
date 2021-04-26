use serde_derive::{Deserialize, Serialize};
use std::convert::TryInto;
use std::fmt::Display;
use std::str::FromStr;

use chrono::{offset::Utc, DateTime, TimeZone};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Deserialize, Serialize, Hash)]
pub struct Timestamp {
    time: Option<DateTime<Utc>>,
}

impl Timestamp {
    pub fn from_nanoseconds(nanoseconds: u64) -> Timestamp {
        if nanoseconds == 0 {
            Timestamp { time: None }
        } else {
            Timestamp {
                time: Some(Utc.timestamp_nanos(nanoseconds.try_into().unwrap())),
            }
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
            "{}",
            self.time
                .map_or("NoTimestamp".to_string(), |time| time.to_rfc3339())
        )
    }
}

impl FromStr for Timestamp {
    type Err = <u64 as FromStr>::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let seconds = u64::from_str(s)?;
        Ok(Timestamp::from_nanoseconds(seconds))
    }
}

impl Default for Timestamp {
    fn default() -> Self {
        Timestamp { time: None }
    }
}
