use std::{cmp::Ordering, convert::TryFrom};

use tendermint_proto::DomainType;

use crate::ics02_client::error::{Error, Kind};
use ibc_proto::ibc::core::client::v1::Height as RawHeight;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Height {
    pub version_number: u64,
    pub version_height: u64,
}

impl Height {
    pub fn new(version_number: u64, version_height: u64) -> Self {
        Self {
            version_number,
            version_height,
        }
    }

    pub fn zero() -> Height {
        Self {
            version_number: 0,
            version_height: 0,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.version_height == 0
    }

    pub fn add(&self, delta: u64) -> Height {
        Height {
            version_number: self.version_number,
            version_height: self.version_height + delta,
        }
    }

    pub fn increment(&self) -> Height {
        self.add(1)
    }

    pub fn sub(&self, delta: u64) -> Result<Height, Error> {
        if self.version_height <= delta {
            return Err(Kind::InvalidHeightResult
                .context("height cannot end up zero or negative")
                .into());
        }

        Ok(Height {
            version_number: self.version_number,
            version_height: self.version_height - delta,
        })
    }

    pub fn decrement(&self) -> Result<Height, Error> {
        self.sub(1)
    }
}

impl Default for Height {
    fn default() -> Self {
        Self::zero()
    }
}

impl PartialOrd for Height {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Height {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.version_number < other.version_number {
            Ordering::Less
        } else if self.version_number > other.version_number {
            Ordering::Greater
        } else if self.version_height < other.version_height {
            Ordering::Less
        } else if self.version_height > other.version_height {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl DomainType<RawHeight> for Height {}

impl TryFrom<RawHeight> for Height {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawHeight) -> Result<Self, Self::Error> {
        Ok(Height {
            version_number: msg.version_number,
            version_height: msg.version_height,
        })
    }
}

impl From<Height> for RawHeight {
    fn from(ics_height: Height) -> Self {
        RawHeight {
            version_number: ics_height.version_number,
            version_height: ics_height.version_height,
        }
    }
}

impl std::fmt::Display for Height {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "epoch: {}, height: {}",
            self.version_number, self.version_height
        )
    }
}
