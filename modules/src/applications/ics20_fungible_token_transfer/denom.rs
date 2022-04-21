#![allow(unused)]

use core::fmt;
use core::ops::Add;
use core::str::FromStr;

use derive_more::{Display, From, FromStr};
use ibc_proto::cosmos::base::v1beta1::Coin as RawCoin;
use ibc_proto::ibc::applications::transfer::v1::DenomTrace as RawDenomTrace;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use super::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::serializers::serde_string;

const IBC_DENOM_PREFIX: &str = "ibc/";

/// A `Coin` type with fully qualified `DenomTrace`.
pub type PrefixedCoin = Coin<DenomTrace>;

/// A `Coin` type with a `HashedDenom`.
pub type HashedCoin = Coin<HashedDenom>;

/// A `Coin` type with an unprefixed denomination.
pub type BaseCoin = Coin<Denom>;

/// Base denomination type
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize, Display)]
#[serde(transparent)]
pub struct Denom(String);

impl FromStr for Denom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.trim().is_empty() {
            Err(Error::empty_base_denom())
        } else if s.contains('/') {
            Err(Error::invalid_base_denom())
        } else {
            Ok(Denom(s.to_owned()))
        }
    }
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct TracePrefix {
    port_id: PortId,
    channel_id: ChannelId,
}

impl TracePrefix {
    pub fn new(port_id: PortId, channel_id: ChannelId) -> Self {
        Self {
            port_id,
            channel_id,
        }
    }
}

impl fmt::Display for TracePrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.port_id, self.channel_id)
    }
}

/// A full trace path modelled as a collection of `TracePrefix`s.
#[derive(Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord, From)]
pub struct TracePath(Vec<TracePrefix>);

impl<'a> TryFrom<Vec<&'a str>> for TracePath {
    type Error = Error;

    fn try_from(v: Vec<&'a str>) -> Result<Self, Self::Error> {
        if v.is_empty() || v.len() % 2 != 0 {
            return Err(Error::invalid_trace_length(v.len()));
        }

        let mut trace = vec![];
        let id_pairs = v.windows(2).map(|paths| (paths[0], paths[1]));
        for (pos, (port_id, channel_id)) in id_pairs.enumerate() {
            let port_id =
                PortId::from_str(port_id).map_err(|e| Error::invalid_trace_port_id(pos, e))?;
            let channel_id = ChannelId::from_str(channel_id)
                .map_err(|e| Error::invalid_trace_channel_id(pos, e))?;
            trace.push(TracePrefix {
                port_id,
                channel_id,
            });
        }

        Ok(trace.into())
    }
}

impl FromStr for TracePath {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts: Vec<&str> = s.split('/').collect();
        parts.try_into()
    }
}

impl fmt::Display for TracePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = self
            .0
            .iter()
            .map(|prefix| prefix.to_string())
            .collect::<Vec<String>>()
            .join("/");
        write!(f, "{}", path)
    }
}

/// A type that contains the base denomination for ICS20 and the source tracing information path.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Deserialize)]
pub struct DenomTrace {
    /// A series of `{port-id}/{channel-id}`s for tracing the source of the token.
    #[serde(with = "serde_string")]
    trace_path: TracePath,
    /// Base denomination of the relayed fungible token.
    base_denom: Denom,
}

impl DenomTrace {
    /// Returns a coin denomination for an ICS20 fungible token in the format
    /// 'ibc/{Hash(trace_path/base_denom)}'.
    pub fn hashed(&self) -> HashedDenom {
        HashedDenom::from(self)
    }

    /// Returns true iff this path has the specified prefix
    pub fn has_prefix(&self, prefix: &TracePrefix) -> bool {
        self.trace_path
            .0
            .first()
            .map(|p| p == prefix)
            .unwrap_or(false)
    }

    /// Removes the specified prefix from the `trace_path` if there is a match.
    pub fn remove_prefix(&mut self, prefix: &TracePrefix) {
        if self.has_prefix(prefix) {
            self.trace_path.0.drain(..0);
        }
    }

    /// Adds the specified prefix to the `trace_path`.
    pub fn add_prefix(&mut self, prefix: TracePrefix) {
        self.trace_path.0.push(prefix)
    }

    /// Returns true if the `trace_path` is empty and false otherwise.
    pub fn is_trace_empty(&self) -> bool {
        self.trace_path.0.is_empty()
    }

    /// Returns true if the denomination originally came from the receiving chain and false
    /// otherwise.
    pub fn is_receiver_chain_source(&self, prefix: &TracePrefix) -> bool {
        self.has_prefix(prefix)
    }

    /// Returns false if the denomination originally came from the receiving chain and true
    /// otherwise.
    pub fn is_sender_chain_source(&self, prefix: &TracePrefix) -> bool {
        !self.is_receiver_chain_source(prefix)
    }
}

impl FromStr for DenomTrace {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts: Vec<&str> = s.split('/').collect();
        assert!(!parts.is_empty(), "split() never returns an empty iterator");

        let (base_denom, trace_path) = {
            if parts.first().unwrap() == &s {
                (Denom::from_str(s)?, TracePath::default())
            } else {
                let base_denom = Denom::from_str(parts.pop().unwrap())?;
                let trace_path = TracePath::try_from(parts)?;
                (base_denom, trace_path)
            }
        };

        Ok(Self {
            trace_path,
            base_denom,
        })
    }
}

impl TryFrom<RawDenomTrace> for DenomTrace {
    type Error = Error;

    fn try_from(value: RawDenomTrace) -> Result<Self, Self::Error> {
        let base_denom = Denom::from_str(&value.base_denom)?;
        let trace_path = TracePath::from_str(&value.path)?;
        Ok(Self {
            trace_path,
            base_denom,
        })
    }
}

impl From<DenomTrace> for RawDenomTrace {
    fn from(value: DenomTrace) -> Self {
        Self {
            path: value.trace_path.to_string(),
            base_denom: value.base_denom.to_string(),
        }
    }
}

impl From<Denom> for DenomTrace {
    fn from(denom: Denom) -> Self {
        Self {
            trace_path: Default::default(),
            base_denom: denom,
        }
    }
}

impl fmt::Display for DenomTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.trace_path.0.is_empty() {
            write!(f, "{}", self.base_denom)
        } else {
            write!(f, "{}/{}", self.trace_path, self.base_denom)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, From)]
pub struct HashedDenom(Vec<u8>);

impl From<&DenomTrace> for HashedDenom {
    fn from(value: &DenomTrace) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(value.to_string().as_bytes());
        let denom_bytes = hasher.finalize();
        Self(denom_bytes.to_vec())
    }
}

impl fmt::Display for HashedDenom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let denom_hex = String::from_utf8(hex::encode_upper(&self.0)).map_err(|_| fmt::Error)?;
        write!(f, "{}{}", IBC_DENOM_PREFIX, denom_hex)
    }
}

impl FromStr for HashedDenom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s
            .strip_prefix(IBC_DENOM_PREFIX)
            .ok_or_else(Error::missing_denom_ibc_prefix)?;
        let bytes = hex::decode_upper(s).map_err(Error::parse_hex)?;
        Ok(Self(bytes))
    }
}

/// A decimal type for representing token transfer amounts.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Display, From, FromStr, Deserialize,
)]
pub struct Decimal(u64);

// We only provide an `Add<Decimal>` implementation which always panics on overflow.
impl Add<Self> for Decimal {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(
            self.0
                .checked_add(rhs.0)
                .expect("decimal addition overflow"),
        )
    }
}

/// Coin defines a token with a denomination and an amount.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Deserialize)]
pub struct Coin<D> {
    /// Denomination
    pub denom: D,
    /// Amount
    pub amount: Decimal,
}

impl<D: FromStr> TryFrom<RawCoin> for Coin<D>
where
    Error: From<<D as FromStr>::Err>,
{
    type Error = Error;

    fn try_from(proto: RawCoin) -> Result<Coin<D>, Self::Error> {
        let denom = D::from_str(&proto.denom)?;
        let amount = Decimal::from_str(&proto.amount).map_err(Error::invalid_coin_amount)?;
        Ok(Self { denom, amount })
    }
}

impl<D: ToString> From<Coin<D>> for RawCoin {
    fn from(coin: Coin<D>) -> RawCoin {
        RawCoin {
            denom: coin.denom.to_string(),
            amount: coin.amount.to_string(),
        }
    }
}

/// The `Coin` type used in `MsgTransfer`, whose denomination is either hashed or unprefixed.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum IbcCoin {
    Hashed(HashedCoin),
    Base(BaseCoin),
}

impl IbcCoin {
    pub fn amount(&self) -> Decimal {
        match self {
            IbcCoin::Hashed(c) => c.amount,
            IbcCoin::Base(c) => c.amount,
        }
    }
}

impl TryFrom<RawCoin> for IbcCoin {
    type Error = Error;

    fn try_from(proto: RawCoin) -> Result<IbcCoin, Self::Error> {
        if proto.denom.starts_with(IBC_DENOM_PREFIX) {
            Ok(Self::Hashed(HashedCoin::try_from(proto)?))
        } else {
            Ok(Self::Base(BaseCoin::try_from(proto)?))
        }
    }
}

impl From<IbcCoin> for RawCoin {
    fn from(ibc_coin: IbcCoin) -> Self {
        let (denom, amount) = match ibc_coin {
            IbcCoin::Hashed(c) => (c.denom.to_string(), c.amount.to_string()),
            IbcCoin::Base(c) => (c.denom.to_string(), c.amount.to_string()),
        };
        Self { denom, amount }
    }
}

impl From<PrefixedCoin> for IbcCoin {
    fn from(prefixed_coin: PrefixedCoin) -> Self {
        let Coin { denom, amount } = prefixed_coin;
        if !denom.is_trace_empty() {
            IbcCoin::Hashed(HashedCoin {
                denom: denom.hashed(),
                amount,
            })
        } else {
            IbcCoin::Base(BaseCoin {
                denom: denom.base_denom,
                amount,
            })
        }
    }
}
