use core::fmt::{self, Display};
use core::ops::{Add, Sub};
use core::str::FromStr;
use ibc_proto::cosmos::base::v1beta1::Coin;

use crate::error::{handle_generic_error, Error};
use crate::ibc::denom::{derive_ibc_denom, Denom, TaggedDenom, TaggedDenomRef};
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::MonoTagged;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Token {
    pub denom: Denom,
    pub amount: u128,
}

pub type TaggedToken<Chain> = MonoTagged<Chain, Token>;
pub type TaggedTokenRef<'a, Chain> = MonoTagged<Chain, &'a Token>;

pub trait TaggedTokenExt<Chain> {
    fn denom(&self) -> TaggedDenomRef<Chain>;

    fn amount(&self) -> u128;

    fn transfer<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Counterparty, Chain>,
        channel_id: &TaggedChannelIdRef<Counterparty, Chain>,
    ) -> Result<TaggedToken<Counterparty>, Error>;
}

pub trait TaggedDenomExt<Chain> {
    fn with_amount(&self, amount: u128) -> TaggedToken<Chain>;
}

impl Token {
    pub fn new(denom: Denom, amount: u128) -> Self {
        Self { denom, amount }
    }

    pub fn as_coin(&self) -> Coin {
        Coin {
            denom: self.denom.to_string(),
            amount: self.amount.to_string(),
        }
    }
}

impl<Chain> TaggedTokenExt<Chain> for TaggedToken<Chain> {
    fn denom(&self) -> TaggedDenomRef<Chain> {
        self.map_ref(|t| &t.denom)
    }

    fn amount(&self) -> u128 {
        self.value().amount
    }

    fn transfer<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Counterparty, Chain>,
        channel_id: &TaggedChannelIdRef<Counterparty, Chain>,
    ) -> Result<TaggedToken<Counterparty>, Error> {
        let denom = derive_ibc_denom(port_id, channel_id, &self.denom())?;

        Ok(denom.with_amount(self.value().amount))
    }
}

impl<'a, Chain> TaggedTokenExt<Chain> for TaggedTokenRef<'a, Chain> {
    fn denom(&self) -> TaggedDenomRef<Chain> {
        self.map_ref(|t| &t.denom)
    }

    fn amount(&self) -> u128 {
        self.value().amount
    }

    fn transfer<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Counterparty, Chain>,
        channel_id: &TaggedChannelIdRef<Counterparty, Chain>,
    ) -> Result<TaggedToken<Counterparty>, Error> {
        let denom = derive_ibc_denom(port_id, channel_id, &self.denom())?;

        Ok(denom.with_amount(self.value().amount))
    }
}

impl<Chain> TaggedDenomExt<Chain> for TaggedDenom<Chain> {
    fn with_amount(&self, amount: u128) -> TaggedToken<Chain> {
        self.map(|denom| Token {
            denom: denom.clone(),
            amount,
        })
    }
}

impl<'a, Chain> TaggedDenomExt<Chain> for TaggedDenomRef<'a, Chain> {
    fn with_amount(&self, amount: u128) -> TaggedToken<Chain> {
        self.map(|denom| Token {
            denom: (*denom).clone(),
            amount,
        })
    }
}

impl Add<u128> for Token {
    type Output = Self;

    fn add(self, amount: u128) -> Self {
        Self {
            denom: self.denom,
            amount: self.amount + amount,
        }
    }
}

impl Sub<u128> for Token {
    type Output = Self;

    fn sub(self, amount: u128) -> Self {
        Self {
            denom: self.denom,
            amount: self.amount - amount,
        }
    }
}

impl<Chain> Add<u128> for MonoTagged<Chain, Token> {
    type Output = Self;

    fn add(self, amount: u128) -> Self {
        self.map_into(|t| t + amount)
    }
}

impl<Chain> Sub<u128> for MonoTagged<Chain, Token> {
    type Output = Self;

    fn sub(self, amount: u128) -> Self {
        self.map_into(|t| t - amount)
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.amount, self.denom)
    }
}

impl TryFrom<Coin> for Token {
    type Error = Error;

    fn try_from(fee: Coin) -> Result<Self, Error> {
        let denom = Denom::base(&fee.denom);
        let amount = u128::from_str(&fee.amount).map_err(handle_generic_error)?;

        Ok(Token::new(denom, amount))
    }
}
