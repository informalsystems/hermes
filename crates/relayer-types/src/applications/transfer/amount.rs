use core::iter::Sum;
use core::ops::Add;
use core::str::FromStr;
use derive_more::{Display, From, Into};
use serde::{Deserialize, Serialize};

use super::error::Error;
use crate::bigint::U256;
use crate::prelude::*;

/// A type for representing token transfer amounts.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize, Display, From, Into,
)]
pub struct Amount(pub U256);

impl Amount {
    pub fn checked_add(self, rhs: impl Into<Amount>) -> Option<Self> {
        self.0.checked_add(rhs.into().0).map(Self)
    }

    pub fn checked_sub(self, rhs: impl Into<Amount>) -> Option<Self> {
        self.0.checked_sub(rhs.into().0).map(Self)
    }
}

impl Add for Amount {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sum for Amount {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self(U256::from(0)), |a, b| a + b)
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

impl From<u128> for Amount {
    fn from(amount: u128) -> Self {
        Self(amount.into())
    }
}
