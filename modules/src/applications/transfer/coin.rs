use core::fmt::{Display, Error as FmtError, Formatter};
use core::str::{from_utf8, FromStr};
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

impl<D: FromStr> Coin<D>
where
    D::Err: Into<Error>,
{
    pub fn from_string_list(coin_str: &str) -> Result<Vec<Self>, Error> {
        coin_str.split(',').map(FromStr::from_str).collect()
    }
}

impl<D: FromStr> FromStr for Coin<D>
where
    D::Err: Into<Error>,
{
    type Err = Error;

    #[allow(clippy::assign_op_pattern)]
    fn from_str(coin_str: &str) -> Result<Self, Error> {
        // Denominations can be 3 ~ 128 characters long and support letters, followed by either
        // a letter, a number or a separator ('/', ':', '.', '_' or '-').
        // Loosely copy the regex from here:
        // https://github.com/cosmos/cosmos-sdk/blob/v0.45.5/types/coin.go#L760-L762
        let matcher = regex!(br"([0-9]+)([a-zA-Z0-9/:\\._\x2d]+)");

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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}{}", self.amount, self.denom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_raw_coin() -> Result<(), Error> {
        {
            let coin = RawCoin::from_str("123stake")?;
            assert_eq!(coin.denom, "stake");
            assert_eq!(coin.amount, 123u64.into());
        }

        {
            let coin = RawCoin::from_str("1a1")?;
            assert_eq!(coin.denom, "a1");
            assert_eq!(coin.amount, 1u64.into());
        }

        {
            let coin = RawCoin::from_str("0x1/:.\\_-")?;
            assert_eq!(coin.denom, "x1/:.\\_-");
            assert_eq!(coin.amount, 0u64.into());
        }

        {
            // `!` is not allowed
            let res = RawCoin::from_str("0x!");
            assert!(res.is_err());
        }

        Ok(())
    }

    #[test]
    fn test_parse_raw_coin_list() -> Result<(), Error> {
        {
            let coins = RawCoin::from_string_list("123stake,1a1,999den0m")?;
            assert_eq!(coins.len(), 3);

            assert_eq!(coins[0].denom, "stake");
            assert_eq!(coins[0].amount, 123u64.into());

            assert_eq!(coins[1].denom, "a1");
            assert_eq!(coins[1].amount, 1u64.into());

            assert_eq!(coins[2].denom, "den0m");
            assert_eq!(coins[2].amount, 999u64.into());
        }

        Ok(())
    }
}
