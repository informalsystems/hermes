use crate::prelude::*;

use core::fmt::Display;
use core::num::ParseIntError;
use core::ops::{Add, Sub};
use core::str::FromStr;
use core::time::Duration;

use chrono::{offset::Utc, DateTime, TimeZone};
use flex_error::{define_error, TraceError};
use serde_derive::{Deserialize, Serialize};
use tendermint::Time;

pub const ZERO_DURATION: Duration = Duration::from_secs(0);

/// A newtype wrapper over `Option<DateTime<Utc>>` to keep track of
/// IBC packet timeout.
///
/// We use an explicit `Option` type to distinguish this when converting between
/// a `u64` value and a raw timestamp. In protocol buffer, the timestamp is
/// represented as a `u64` Unix timestamp in nanoseconds, with 0 representing the absence
/// of timestamp.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Deserialize, Serialize, Hash)]
pub struct Timestamp {
    time: Option<DateTime<Utc>>,
}

/// The expiry result when comparing two timestamps.
/// - If either timestamp is invalid (0), the result is `InvalidTimestamp`.
/// - If the left timestamp is strictly after the right timestamp, the result is `Expired`.
/// - Otherwise, the result is `NotExpired`.
///
/// User of this result may want to determine whether error should be raised,
/// when either of the timestamp being compared is invalid.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Deserialize, Serialize, Hash)]
pub enum Expiry {
    Expired,
    NotExpired,
    InvalidTimestamp,
}

impl Timestamp {
    /// The IBC protocol represents timestamps as u64 Unix
    /// timestamps in nanoseconds.
    ///
    /// A protocol value of 0 indicates that the timestamp
    /// is not set. In this case, our domain type takes the
    /// value of None.
    ///
    pub fn from_nanoseconds(nanoseconds: u64) -> Result<Timestamp, ParseTimestampError> {
        if nanoseconds == 0 {
            Ok(Timestamp { time: None })
        } else {
            // The underlying library [`chrono::DateTime`] does not support
            // conversion from `u64` nanoseconds value, only from `i64`
            // (which can overflow when converting from the unsigned type).
            // We go around this limitation by decomposing the `u64` nanos
            // into seconds + nanos and constructing the timestamp from that.
            let (s, ns) = util::break_in_secs_and_nanos(nanoseconds);

            match Utc.timestamp_opt(s, ns) {
                chrono::LocalResult::None => {
                    Err(ParseTimestampError::invalid_timestamp_conversion(s, ns))
                }
                chrono::LocalResult::Single(ts) => Ok(Timestamp { time: Some(ts) }),
                chrono::LocalResult::Ambiguous(_, _) => {
                    Err(ParseTimestampError::ambiguous_timestamp_conversion(s, ns))
                }
            }
        }
    }

    /// Returns a `Timestamp` representation of the current time.
    pub fn now() -> Timestamp {
        Timestamp {
            time: Some(Utc::now()),
        }
    }

    /// Returns a `Timestamp` representation of a timestamp not being set.
    pub fn none() -> Self {
        Timestamp { time: None }
    }

    /// Computes the duration difference of another `Timestamp` from the current one.
    /// Returns the difference in time as an [`core::time::Duration`].
    /// Returns `None` if the other `Timestamp` is more advanced
    /// than the current or if either of the `Timestamp`s is not set.
    pub fn duration_since(&self, other: &Timestamp) -> Option<Duration> {
        match (self.time, other.time) {
            (Some(time1), Some(time2)) => time1.signed_duration_since(time2).to_std().ok(),
            _ => None,
        }
    }

    /// Convert a `Timestamp` from [`chrono::DateTime<Utc>`].
    pub fn from_datetime(time: DateTime<Utc>) -> Timestamp {
        Timestamp { time: Some(time) }
    }

    /// Convert a `Timestamp` to `u64` value in nanoseconds. If no timestamp
    /// is set, the result is 0.
    /// ```
    /// use ibc::timestamp::Timestamp;
    /// let max = u64::MAX;
    /// let tx = Timestamp::from_nanoseconds(max).unwrap();
    /// let utx = tx.as_nanoseconds();
    /// assert_eq!(utx, max);
    /// let min = u64::MIN;
    /// let ti = Timestamp::from_nanoseconds(min).unwrap();
    /// let uti = ti.as_nanoseconds();
    /// assert_eq!(uti, min);
    /// ```
    pub fn as_nanoseconds(&self) -> u64 {
        self.time.map_or(0, |time| {
            let s = time.timestamp();
            assert!(s >= 0, "time {:?} has negative `.timestamp()`", time);
            let s: u64 = s.try_into().unwrap();

            util::assemble_in_nanos(s, time.timestamp_subsec_nanos())
        })
    }

    /// Convert a `Timestamp` to an optional [`chrono::DateTime<Utc>`]
    pub fn as_datetime(&self) -> Option<DateTime<Utc>> {
        self.time
    }

    /// Checks whether the timestamp has expired when compared to the
    /// `other` timestamp. Returns an [`Expiry`] result.
    pub fn check_expiry(&self, other: &Timestamp) -> Expiry {
        match (self.time, other.time) {
            (Some(time1), Some(time2)) => {
                if time1 > time2 {
                    Expiry::Expired
                } else {
                    Expiry::NotExpired
                }
            }
            _ => Expiry::InvalidTimestamp,
        }
    }

    /// Checks whether the current timestamp is strictly more advanced
    /// than the `other` timestamp. Return true if so, and false
    /// otherwise.
    pub fn after(&self, other: &Timestamp) -> bool {
        match (self.time, other.time) {
            (Some(time1), Some(time2)) => time1 > time2,
            _ => false,
        }
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Timestamp({})",
            self.time
                .map_or("NoTimestamp".to_string(), |time| time.to_rfc3339())
        )
    }
}

define_error! {
    TimestampOverflowError {
        TimestampOverflow
            |_| { "Timestamp overflow when modifying with duration" }
    }
}

impl Add<Duration> for Timestamp {
    type Output = Result<Timestamp, TimestampOverflowError>;

    fn add(self, duration: Duration) -> Result<Timestamp, TimestampOverflowError> {
        match self.as_datetime() {
            Some(datetime) => {
                let duration2 = chrono::Duration::from_std(duration)
                    .map_err(|_| TimestampOverflowError::timestamp_overflow())?;
                Ok(Self::from_datetime(datetime + duration2))
            }
            None => Ok(self),
        }
    }
}

impl Sub<Duration> for Timestamp {
    type Output = Result<Timestamp, TimestampOverflowError>;

    fn sub(self, duration: Duration) -> Result<Timestamp, TimestampOverflowError> {
        match self.as_datetime() {
            Some(datetime) => {
                let duration2 = chrono::Duration::from_std(duration)
                    .map_err(|_| TimestampOverflowError::timestamp_overflow())?;
                Ok(Self::from_datetime(datetime - duration2))
            }
            None => Ok(self),
        }
    }
}

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    ParseTimestampError {
        ParseInt
            [ TraceError<ParseIntError> ]
            | _ | { "error parsing u64 integer from string"},

        InvalidTimestampConversion
            {
                secs: i64,
                nanos: u32,
            }
            | _ | { "error converting into Timestamp from seconds + nanoseconds" },

        AmbiguousTimestampConversion
            {
                secs: i64,
                nanos: u32,
            }
            | _ | { "ambigous conversion into Timestamp from seconds + nanoseconds" },
    }
}

impl FromStr for Timestamp {
    type Err = ParseTimestampError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let nanoseconds = u64::from_str(s).map_err(ParseTimestampError::parse_int)?;

        Timestamp::from_nanoseconds(nanoseconds)
    }
}

impl From<Time> for Timestamp {
    fn from(tendermint_time: Time) -> Timestamp {
        Timestamp {
            time: Some(tendermint_time.into()),
        }
    }
}

impl Default for Timestamp {
    fn default() -> Self {
        Timestamp { time: None }
    }
}

pub mod util {

    const NANOS_PER_SEC: u64 = 1_000_000_000;

    /// Helper for the [`Timestamp::from_nanoseconds`] constructor.
    ///
    /// Converts `u64` nanoseconds into its constituent
    /// seconds (represented as `i64`) plus the remaining
    /// nanoseconds (represented as `u32`).
    ///
    /// Similar to [`chrono::timestamp_nanos`].
    pub(super) fn break_in_secs_and_nanos(nanoseconds: u64) -> (i64, u32) {
        let seconds = nanoseconds / NANOS_PER_SEC;

        // Safe because u64::MAX divided by NANOS_PER_SEC fits into i64
        let out_secs: i64 = seconds.try_into().unwrap();
        let out_nanos = (nanoseconds % NANOS_PER_SEC) as u32;

        (out_secs, out_nanos)
    }

    /// Helper method for achieving the reverse of
    /// [`break_in_secs_and_nanos`].
    ///
    pub(super) fn assemble_in_nanos(s: u64, subsec_ns: u32) -> u64 {
        let ns = s * NANOS_PER_SEC;

        ns + subsec_ns as u64
    }
}

#[cfg(test)]
mod tests {
    use chrono::Utc;

    use core::time::Duration;
    use std::thread::sleep;
    use test_env_log::test;

    use super::{Expiry, Timestamp, ZERO_DURATION};

    #[test]
    fn test_timestamp_comparisons() {
        let nil_timestamp = Timestamp::from_nanoseconds(0).unwrap();
        assert_eq!(nil_timestamp.time, None);
        assert_eq!(nil_timestamp.as_nanoseconds(), 0);

        let timestamp1 = Timestamp::from_nanoseconds(1).unwrap();
        assert_eq!(timestamp1.time.unwrap().timestamp(), 0);
        assert_eq!(timestamp1.time.unwrap().timestamp_millis(), 0);
        assert_eq!(timestamp1.time.unwrap().timestamp_nanos(), 1);
        assert_eq!(timestamp1.as_nanoseconds(), 1);

        let timestamp2 = Timestamp::from_nanoseconds(1_000_000_000).unwrap();
        assert_eq!(timestamp2.time.unwrap().timestamp(), 1);
        assert_eq!(timestamp2.time.unwrap().timestamp_millis(), 1_000);
        assert_eq!(timestamp2.as_nanoseconds(), 1_000_000_000);

        assert!(Timestamp::from_nanoseconds(u64::MAX).is_ok());
        assert!(Timestamp::from_nanoseconds(i64::MAX.try_into().unwrap()).is_ok());

        assert_eq!(timestamp1.check_expiry(&timestamp2), Expiry::NotExpired);
        assert_eq!(timestamp1.check_expiry(&timestamp1), Expiry::NotExpired);
        assert_eq!(timestamp2.check_expiry(&timestamp2), Expiry::NotExpired);
        assert_eq!(timestamp2.check_expiry(&timestamp1), Expiry::Expired);
        assert_eq!(
            timestamp1.check_expiry(&nil_timestamp),
            Expiry::InvalidTimestamp
        );
        assert_eq!(
            nil_timestamp.check_expiry(&timestamp2),
            Expiry::InvalidTimestamp
        );
        assert_eq!(
            nil_timestamp.check_expiry(&nil_timestamp),
            Expiry::InvalidTimestamp
        );
    }

    #[test]
    fn test_timestamp_arithmetic() {
        let time0 = Timestamp::none();
        let time1 = Timestamp::from_nanoseconds(100).unwrap();
        let time2 = Timestamp::from_nanoseconds(150).unwrap();
        let time3 = Timestamp::from_nanoseconds(50).unwrap();
        let duration = Duration::from_nanos(50);

        assert_eq!(time1, (time1 + ZERO_DURATION).unwrap());
        assert_eq!(time2, (time1 + duration).unwrap());
        assert_eq!(time3, (time1 - duration).unwrap());
        assert_eq!(time0, (time0 + duration).unwrap());
        assert_eq!(time0, (time0 - duration).unwrap());
    }

    #[test]
    fn subtract_compare() {
        let sleep_duration = Duration::from_micros(100);

        let start = Timestamp::from_datetime(Utc::now());
        sleep(sleep_duration);
        let end = Timestamp::from_datetime(Utc::now());

        let res = end.duration_since(&start);
        assert!(res.is_some());

        let inner = res.unwrap();
        assert!(inner > sleep_duration);
    }
}
