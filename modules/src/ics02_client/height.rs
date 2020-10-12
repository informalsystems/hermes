use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;

use tendermint_proto::DomainType;

use crate::ics02_client::error::{Error, Kind};
use ibc_proto::ibc::client::Height as RawHeight;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Height {
    pub version_number: u64,
    pub version_height: u64,
}

pub fn zero_height() -> Height {
    Default::default()
}

impl Height {
    pub fn new(version_number: u64, version_height: u64) -> Self {
        Height {
            version_number,
            version_height,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.version_height == 0
    }

    fn compare(&self, other: Height) -> i8 {
        if self.version_number < other.version_number {
            -1
        } else if self.version_number > other.version_number {
            1
        } else if self.version_height < other.version_height {
            -1
        } else if self.version_height > other.version_height {
            1
        } else {
            0
        }
    }

    pub fn gt(&self, other: Height) -> bool {
        self.compare(other) > 0
    }

    pub fn gte(&self, other: Height) -> bool {
        self.compare(other) >= 0
    }

    pub fn lt(&self, other: Height) -> bool {
        self.compare(other) < 0
    }

    pub fn lte(&self, other: Height) -> bool {
        self.compare(other) <= 0
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

impl DomainType<RawHeight> for Height {}

impl TryFrom<RawHeight> for Height {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawHeight) -> Result<Self, Self::Error> {
        Ok(Height {
            version_number: msg.epoch_number,
            version_height: msg.epoch_height,
        })
    }
}

impl From<Height> for RawHeight {
    fn from(ics_height: Height) -> Self {
        RawHeight {
            epoch_number: ics_height.version_number,
            epoch_height: ics_height.version_height,
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

/// is_epoch_format() checks if a chain_id is in the format required for parsing epochs
/// The chainID must be in the form: `{chainID}-{version}
fn is_epoch_format(chain_id: String) -> bool {
    use regex::Regex;
    let re = Regex::new(r"^.+[^-]-{1}[1-9][0-9]*$").unwrap();
    re.is_match(chain_id.as_str())
}

pub fn chain_version(chain_id: String) -> u64 {
    if !is_epoch_format(chain_id.clone()) {
        return 0;
    }
    let split: Vec<_> = chain_id.split('-').collect();
    split[1].parse().unwrap_or(0)
}
