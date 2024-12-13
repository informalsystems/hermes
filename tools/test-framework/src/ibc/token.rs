use core::ops::{Add, Sub};
use ibc_relayer_types::applications::transfer::amount::Amount;
use ibc_relayer_types::applications::transfer::coin::{Coin, RawCoin};

use crate::error::Error;
use crate::ibc::denom::{derive_ibc_denom, Denom, TaggedDenom, TaggedDenomRef};
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::MonoTagged;

pub type Token = Coin<Denom>;

pub type TaggedToken<Chain> = MonoTagged<Chain, Token>;
pub type TaggedTokenRef<'a, Chain> = MonoTagged<Chain, &'a Token>;

pub trait TaggedTokenExt<Chain> {
    fn denom(&self) -> TaggedDenomRef<Chain>;

    fn amount(&self) -> Amount;

    fn as_coin(&self) -> RawCoin;

    fn transfer<Counterparty>(
        &self,
        port_id: &TaggedPortIdRef<Counterparty, Chain>,
        channel_id: &TaggedChannelIdRef<Counterparty, Chain>,
    ) -> Result<TaggedToken<Counterparty>, Error>;
}

pub trait TaggedDenomExt<Chain> {
    fn with_amount(&self, amount: impl Into<Amount>) -> TaggedToken<Chain>;
}

impl<Chain> TaggedTokenExt<Chain> for TaggedToken<Chain> {
    fn denom(&self) -> TaggedDenomRef<Chain> {
        self.map_ref(|t| &t.denom)
    }

    fn amount(&self) -> Amount {
        self.value().amount
    }

    fn as_coin(&self) -> RawCoin {
        RawCoin::new(self.value().denom.to_string(), self.value().amount)
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

    fn amount(&self) -> Amount {
        self.value().amount
    }

    fn as_coin(&self) -> RawCoin {
        RawCoin::new(self.value().denom.to_string(), self.value().amount)
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
    fn with_amount(&self, amount: impl Into<Amount>) -> TaggedToken<Chain> {
        self.map(|denom| Token {
            denom: denom.clone(),
            amount: amount.into(),
        })
    }
}

impl<'a, Chain> TaggedDenomExt<Chain> for TaggedDenomRef<'a, Chain> {
    fn with_amount(&self, amount: impl Into<Amount>) -> TaggedToken<Chain> {
        self.map(|denom| Token {
            denom: (*denom).clone(),
            amount: amount.into(),
        })
    }
}

impl<Chain, I: Into<Amount>> Add<I> for MonoTagged<Chain, Token> {
    type Output = Self;

    fn add(self, amount: I) -> Self {
        self.map_into(|t| t.checked_add(amount))
            .transpose()
            .unwrap()
    }
}

impl<Chain, I: Into<Amount>> Sub<I> for MonoTagged<Chain, Token> {
    type Output = Self;

    fn sub(self, amount: I) -> Self {
        self.map_into(|t| t.checked_sub(amount))
            .transpose()
            .unwrap()
    }
}
