use std::cmp::Ordering;
use std::convert::TryFrom;
use std::prelude::v1::format;
use std::str::FromStr;
use std::string::String;
use std::vec::Vec;

use serde_derive::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::Height as RawHeight;

use crate::ics02_client::error::{self, ClientError};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Height {
    /// Previously known as "epoch"
    pub revision_number: u64,

    /// The height of a block
    pub revision_height: u64,
}

impl Height {
    pub fn new(revision_number: u64, revision_height: u64) -> Self {
        Self {
            revision_number,
            revision_height,
        }
    }

    pub fn zero() -> Height {
        Self {
            revision_number: 0,
            revision_height: 0,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.revision_height == 0
    }

    pub fn add(&self, delta: u64) -> Height {
        Height {
            revision_number: self.revision_number,
            revision_height: self.revision_height + delta,
        }
    }

    pub fn increment(&self) -> Height {
        self.add(1)
    }

    pub fn sub(&self, delta: u64) -> Result<Height, ClientError> {
        if self.revision_height <= delta {
            return Err(error::invalid_height_result_error(anyhow::anyhow!(
                "height cannot end up zero or negative"
            )));
        }

        Ok(Height {
            revision_number: self.revision_number,
            revision_height: self.revision_height - delta,
        })
    }

    pub fn decrement(&self) -> Result<Height, ClientError> {
        self.sub(1)
    }

    pub fn with_revision_height(self, revision_height: u64) -> Height {
        Height {
            revision_height,
            ..self
        }
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

impl Protobuf<RawHeight> for Height {}

impl TryFrom<RawHeight> for Height {
    type Error = ClientError;

    fn try_from(raw: RawHeight) -> Result<Self, Self::Error> {
        Ok(Height {
            revision_number: raw.revision_number,
            revision_height: raw.revision_height,
        })
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

impl std::fmt::Debug for Height {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Height")
            .field("revision", &self.revision_number)
            .field("height", &self.revision_height)
            .finish()
    }
}

/// Custom debug output to omit the packet data
impl std::fmt::Display for Height {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}-{}", self.revision_number, self.revision_height)
    }
}

impl TryFrom<&str> for Height {
    type Error = ClientError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let split: Vec<&str> = value.split('-').collect();
        Ok(Height {
            revision_number: split[0].parse::<u64>().unwrap(),
            revision_height: split[1].parse::<u64>().unwrap(),
        })
    }
}

impl From<Height> for String {
    fn from(height: Height) -> Self {
        format!("{}-{}", height.revision_number, height.revision_number)
    }
}

impl FromStr for Height {
    type Err = ClientError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Height::try_from(s)
    }
}
