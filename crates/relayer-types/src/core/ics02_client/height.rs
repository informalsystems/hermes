use crate::prelude::*;
use core::cmp::Ordering;

use core::num::ParseIntError;
use core::str::FromStr;

use flex_error::{define_error, TraceError};
use ibc_proto::protobuf::Protobuf;
use serde_derive::{Deserialize, Serialize};

use ibc_proto::ibc::core::client::v1::Height as RawHeight;

use crate::core::ics02_client::error::Error;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Height {
    /// Previously known as "epoch"
    revision_number: u64,

    /// The height of a block
    revision_height: u64,
}

impl Height {
    pub fn new(revision_number: u64, revision_height: u64) -> Result<Self, Error> {
        if revision_height == 0 {
            return Err(Error::invalid_height());
        }

        Ok(Self {
            revision_number,
            revision_height,
        })
    }

    pub fn revision_number(&self) -> u64 {
        self.revision_number
    }

    pub fn revision_height(&self) -> u64 {
        self.revision_height
    }

    pub fn increment(self) -> Height {
        self + 1
    }

    pub fn decrement(self) -> Result<Height, Error> {
        self - 1
    }
}

impl PartialOrd for Height {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Height {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.revision_number < other.revision_number {
            Ordering::Less
        } else if self.revision_number > other.revision_number {
            Ordering::Greater
        } else if self.revision_height < other.revision_height {
            Ordering::Less
        } else if self.revision_height > other.revision_height {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl core::ops::Add<u64> for Height {
    type Output = Self;

    fn add(self, rhs: u64) -> Self::Output {
        Self {
            revision_number: self.revision_number,
            revision_height: self.revision_height + rhs,
        }
    }
}

impl core::ops::Sub<u64> for Height {
    type Output = Result<Self, Error>;

    fn sub(self, delta: u64) -> Self::Output {
        if self.revision_height <= delta {
            return Err(Error::invalid_height_result());
        }

        Ok(Height {
            revision_number: self.revision_number,
            revision_height: self.revision_height - delta,
        })
    }
}

impl Protobuf<RawHeight> for Height {}

impl TryFrom<RawHeight> for Height {
    type Error = Error;

    fn try_from(raw_height: RawHeight) -> Result<Self, Self::Error> {
        Height::new(raw_height.revision_number, raw_height.revision_height)
    }
}

impl From<Height> for RawHeight {
    fn from(ics_height: Height) -> Self {
        RawHeight {
            revision_number: ics_height.revision_number,
            revision_height: ics_height.revision_height,
        }
    }
}

impl core::fmt::Debug for Height {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("Height")
            .field("revision", &self.revision_number)
            .field("height", &self.revision_height)
            .finish()
    }
}

/// Custom debug output to omit the packet data
impl core::fmt::Display for Height {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}-{}", self.revision_number, self.revision_height)
    }
}

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    HeightError {
        HeightConversion
            { height: String }
            [ TraceError<ParseIntError> ]
            | e | {
                format_args!("cannot convert into a `Height` type from string {0}",
                    e.height)
            },
        ZeroHeight
            |_| { "attempted to parse an invalid zero height" }
    }
}

impl TryFrom<&str> for Height {
    type Error = HeightError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let split: Vec<&str> = value.split('-').collect();

        let revision_number = split[0]
            .parse::<u64>()
            .map_err(|e| HeightError::height_conversion(value.to_owned(), e))?;
        let revision_height = split[1]
            .parse::<u64>()
            .map_err(|e| HeightError::height_conversion(value.to_owned(), e))?;

        Height::new(revision_number, revision_height).map_err(|_| HeightError::zero_height())
    }
}

impl From<Height> for String {
    fn from(height: Height) -> Self {
        format!("{}-{}", height.revision_number, height.revision_height)
    }
}

impl FromStr for Height {
    type Err = HeightError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Height::try_from(s)
    }
}
