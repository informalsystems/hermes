use crate::prelude::*;

use core::fmt::{Display, Error as FmtError, Formatter};
use core::hash::{Hash, Hasher};
use core::num::ParseIntError;
use core::ops::{Add, Sub};
use core::str::FromStr;
use core::time::Duration;

use flex_error::{define_error, TraceError};
use serde_derive::{Deserialize, Serialize};
use tendermint::Time;
use time::OffsetDateTime;

pub const ZERO_DURATION: Duration = Duration::from_secs(0);

/// A newtype wrapper over `Option<Time>` to keep track of
/// IBC packet timeout.
///
/// We use an explicit `Option` type to distinguish this when converting between
/// a `u64` value and a raw timestamp. In protocol buffer, the timestamp is
/// represented as a `u64` Unix timestamp in nanoseconds, with 0 representing the absence
/// of timestamp.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Default, Deserialize, Serialize)]
pub struct Timestamp {
    time: Option<Time>,
}

// TODO: derive when tendermint::Time supports it:
// https://github.com/informalsystems/tendermint-rs/pull/1054
#[allow(clippy::derived_hash_with_manual_eq)]
impl Hash for Timestamp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let odt: Option<OffsetDateTime> = self.time.map(Into::into);
        odt.hash(state);
    }
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
            // As the `u64` representation can only represent times up to
            // about year 2554, there is no risk of overflowing `Time`
            // or `OffsetDateTime`.
            let ts = OffsetDateTime::from_unix_timestamp_nanos(nanoseconds as i128)
                .unwrap()
                .try_into()
                .unwrap();
            Ok(Timestamp { time: Some(ts) })
        }
    }

    /// Returns a `Timestamp` representation of the current time.
    #[cfg(feature = "clock")]
    pub fn now() -> Timestamp {
        Time::now().into()
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
            (Some(time1), Some(time2)) => time1.duration_since(time2).ok(),
            _ => None,
        }
    }

    /// Convert a `Timestamp` to `u64` value in nanoseconds. If no timestamp
    /// is set, the result is 0.
    ///
    #[deprecated(since = "0.9.1", note = "use `nanoseconds` instead")]
    pub fn as_nanoseconds(&self) -> u64 {
        (*self).nanoseconds()
    }

    /// Convert a `Timestamp` to `u64` value in nanoseconds. If no timestamp
    /// is set, the result is 0.
    /// ```
    /// use ibc_relayer_types::timestamp::Timestamp;
    ///
    /// let max = u64::MAX;
    /// let tx = Timestamp::from_nanoseconds(max).unwrap();
    /// let utx = tx.nanoseconds();
    /// assert_eq!(utx, max);
    /// let min = u64::MIN;
    /// let ti = Timestamp::from_nanoseconds(min).unwrap();
    /// let uti = ti.nanoseconds();
    /// assert_eq!(uti, min);
    /// let tz = Timestamp::default();
    /// let utz = tz.nanoseconds();
    /// assert_eq!(utz, 0);
    /// ```
    pub fn nanoseconds(self) -> u64 {
        self.time.map_or(0, |time| {
            let t: OffsetDateTime = time.into();
            let s = t.unix_timestamp_nanos();
            assert!(s >= 0, "time {time:?} has negative `.timestamp()`");
            s.try_into().unwrap()
        })
    }

    /// Convert a `Timestamp` to an optional [`OffsetDateTime`]
    pub fn into_datetime(self) -> Option<OffsetDateTime> {
        self.time.map(Into::into)
    }

    /// Convert a `Timestamp` to an optional [`tendermint::Time`]
    pub fn into_tm_time(self) -> Option<Time> {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Timestamp({})",
            self.time
                .map_or("NoTimestamp".to_string(), |time| time.to_rfc3339())
        )
    }
}

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    TimestampOverflowError {
        TimestampOverflow
            |_| { "Timestamp overflow when modifying with duration" }
    }
}

impl Add<Duration> for Timestamp {
    type Output = Result<Timestamp, TimestampOverflowError>;

    fn add(self, duration: Duration) -> Result<Timestamp, TimestampOverflowError> {
        match self.time {
            Some(time) => {
                let time =
                    (time + duration).map_err(|_| TimestampOverflowError::timestamp_overflow())?;
                Ok(Timestamp { time: Some(time) })
            }
            None => Ok(self),
        }
    }
}

impl Sub<Duration> for Timestamp {
    type Output = Result<Timestamp, TimestampOverflowError>;

    fn sub(self, duration: Duration) -> Result<Timestamp, TimestampOverflowError> {
        match self.time {
            Some(time) => {
                let time =
                    (time - duration).map_err(|_| TimestampOverflowError::timestamp_overflow())?;
                Ok(Timestamp { time: Some(time) })
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
            time: Some(tendermint_time),
        }
    }
}

#[cfg(test)]
mod tests {
    use time::OffsetDateTime;

    use core::time::Duration;
    use std::thread::sleep;
    use test_log::test;

    use super::{Expiry, Timestamp, ZERO_DURATION};

    #[test]
    fn test_timestamp_comparisons() {
        let nil_timestamp = Timestamp::from_nanoseconds(0).unwrap();
        assert_eq!(nil_timestamp.time, None);
        assert_eq!(nil_timestamp.nanoseconds(), 0);

        let timestamp1 = Timestamp::from_nanoseconds(1).unwrap();
        let dt: OffsetDateTime = timestamp1.time.unwrap().into();
        assert_eq!(dt.unix_timestamp_nanos(), 1);
        assert_eq!(timestamp1.nanoseconds(), 1);

        let timestamp2 = Timestamp::from_nanoseconds(1_000_000_000).unwrap();
        let dt: OffsetDateTime = timestamp2.time.unwrap().into();
        assert_eq!(dt.unix_timestamp_nanos(), 1_000_000_000);
        assert_eq!(timestamp2.nanoseconds(), 1_000_000_000);

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

        let start = Timestamp::now();
        sleep(sleep_duration);
        let end = Timestamp::now();

        let res = end.duration_since(&start);
        assert!(res.is_some());

        let inner = res.unwrap();
        assert!(inner > sleep_duration);
    }
}
