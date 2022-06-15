use core::fmt::{self, Display};
use core::str::from_utf8;
use core::str::FromStr;
use ibc_proto::cosmos::base::v1beta1::Coin as ProtoCoin;
use safe_regex::regex;
use serde::{Deserialize, Serialize};

use super::amount::Amount;
use super::denom::{BaseDenom, PrefixedDenom};
use super::error::Error;
use crate::prelude::*;
use crate::serializers::serde_string;

/// A `Coin` type with fully qualified `PrefixedDenom`.
pub type PrefixedCoin = Coin<PrefixedDenom>;

/// A `Coin` type with an unprefixed denomination.
pub type BaseCoin = Coin<BaseDenom>;

pub type RawCoin = Coin<String>;

/// Coin defines a token with a denomination and an amount.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Coin<D> {
    /// Denomination
    pub denom: D,
    /// Amount
    #[serde(with = "serde_string")]
    pub amount: Amount,
}

impl<D> Coin<D> {
    pub fn new(denom: D, amount: impl Into<Amount>) -> Self {
        Self {
            denom,
            amount: amount.into(),
        }
    }

    pub fn checked_add(self, rhs: impl Into<Amount>) -> Option<Self> {
        let amount = self.amount.checked_add(rhs)?;
        Some(Self::new(self.denom, amount))
    }

    pub fn checked_sub(self, rhs: impl Into<Amount>) -> Option<Self> {
        let amount = self.amount.checked_sub(rhs)?;
        Some(Self::new(self.denom, amount))
    }
}

impl<D: FromStr> FromStr for Coin<D>
where
    D::Err: Into<Error>,
{
    type Err = Error;

    #[allow(clippy::assign_op_pattern)]
    fn from_str(coin_str: &str) -> Result<Self, Error> {
        let matcher = regex!(br"(\\d+)([a-zA-Z].+)");

        let (m1, m2) = matcher
            .match_slices(coin_str.as_bytes())
            .ok_or_else(|| Error::invalid_coin(coin_str.to_string()))?;

        let amount = from_utf8(m1).map_err(Error::utf8_decode)?.parse()?;

        let denom = from_utf8(m2)
            .map_err(Error::utf8_decode)?
            .parse()
            .map_err(Into::into)?;

        Ok(Coin { amount, denom })
    }
}

impl<D: FromStr> Coin<D>
where
    D::Err: Into<Error>,
{
    pub fn from_string_list(coin_str: &str) -> Result<Vec<Self>, Error> {
        coin_str.split(',').map(FromStr::from_str).collect()
    }
}

impl<D: FromStr> TryFrom<ProtoCoin> for Coin<D>
where
    D::Err: Into<Error>,
{
    type Error = Error;

    fn try_from(proto: ProtoCoin) -> Result<Coin<D>, Self::Error> {
        let denom = D::from_str(&proto.denom).map_err(Into::into)?;
        let amount = Amount::from_str(&proto.amount)?;
        Ok(Self { denom, amount })
    }
}

impl<D: ToString> From<Coin<D>> for ProtoCoin {
    fn from(coin: Coin<D>) -> ProtoCoin {
        ProtoCoin {
            denom: coin.denom.to_string(),
            amount: coin.amount.to_string(),
        }
    }
}

impl From<BaseCoin> for PrefixedCoin {
    fn from(coin: BaseCoin) -> PrefixedCoin {
        PrefixedCoin {
            denom: coin.denom.into(),
            amount: coin.amount,
        }
    }
}

impl<D: Display> Display for Coin<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.amount, self.denom)
    }
}
