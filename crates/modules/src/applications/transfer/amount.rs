use core::str::FromStr;
use derive_more::{Display, From, Into};
use serde::{Deserialize, Serialize};

use super::error::Error;
use crate::bigint::U256;

/// A type for representing token transfer amounts.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize, Display, From, Into,
)]
pub struct Amount(U256);

impl Amount {
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(Self)
    }

    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(Self)
    }
}

impl FromStr for Amount {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let amount = U256::from_dec_str(s).map_err(Error::invalid_amount)?;
        Ok(Self(amount))
    }
}

impl From<u64> for Amount {
    fn from(v: u64) -> Self {
        Self(v.into())
    }
}
