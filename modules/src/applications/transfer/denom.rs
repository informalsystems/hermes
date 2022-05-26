use core::fmt;
use core::str::FromStr;

use derive_more::{Display, From, Into};
use ibc_proto::cosmos::base::v1beta1::Coin as RawCoin;
use ibc_proto::ibc::applications::transfer::v1::DenomTrace as RawDenomTrace;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use super::error::Error;
use crate::bigint::U256;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::serializers::serde_string;

const IBC_DENOM_PREFIX: &str = "ibc";

/// A `Coin` type with fully qualified `PrefixedDenom`.
pub type PrefixedCoin = Coin<PrefixedDenom>;

/// A `Coin` type with a `HashedDenom`.
pub type HashedCoin = Coin<HashedDenom>;

/// A `Coin` type with an unprefixed denomination.
pub type BaseCoin = Coin<BaseDenom>;

/// Base denomination type
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize, Display)]
#[serde(transparent)]
pub struct BaseDenom(String);

impl FromStr for BaseDenom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.trim().is_empty() {
            Err(Error::empty_base_denom())
        } else {
            Ok(BaseDenom(s.to_owned()))
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
// Internally, the `TracePath` is modelled as a `Vec<TracePrefix>` but with the order reversed, i.e.
// "transfer/channel-0/transfer/channel-1/uatom" => `["transfer/channel-1", "transfer/channel-0"]`
// This is done for ease of addition/removal of prefixes.
#[derive(Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord, From)]
pub struct TracePath(Vec<TracePrefix>);

impl TracePath {
    /// Returns true iff this path starts with the specified prefix
    pub fn starts_with(&self, prefix: &TracePrefix) -> bool {
        self.0.last().map(|p| p == prefix).unwrap_or(false)
    }

    /// Removes the specified prefix from the path if there is a match, otherwise does nothing.
    pub fn remove_prefix(&mut self, prefix: &TracePrefix) {
        if self.starts_with(prefix) {
            self.0.pop();
        }
    }

    /// Adds the specified prefix to the path.
    pub fn add_prefix(&mut self, prefix: TracePrefix) {
        self.0.push(prefix)
    }

    /// Returns true if the path is empty and false otherwise.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a> TryFrom<Vec<&'a str>> for TracePath {
    type Error = Error;

    fn try_from(v: Vec<&'a str>) -> Result<Self, Self::Error> {
        if v.len() % 2 != 0 {
            return Err(Error::invalid_trace_length(v.len()));
        }

        let mut trace = vec![];
        let id_pairs = v.chunks_exact(2).map(|paths| (paths[0], paths[1]));
        for (pos, (port_id, channel_id)) in id_pairs.rev().enumerate() {
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
        let parts = {
            let parts: Vec<&str> = s.split('/').collect();
            if parts.len() == 1 && parts[0].trim().is_empty() {
                vec![]
            } else {
                parts
            }
        };
        parts.try_into()
    }
}

impl fmt::Display for TracePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = self
            .0
            .iter()
            .rev()
            .map(|prefix| prefix.to_string())
            .collect::<Vec<String>>()
            .join("/");
        write!(f, "{}", path)
    }
}

/// Indicates whether the sender chain is acting as a source or sink. Each send to any chain other
/// than the one it was previously received from is a movement forwards in the token's timeline. In
/// these instances the sender chain is acting as the source zone.
pub enum Source {
    Sender,
    Receiver,
}

/// A type that contains the base denomination for ICS20 and the source tracing information path.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PrefixedDenom {
    /// A series of `{port-id}/{channel-id}`s for tracing the source of the token.
    #[serde(with = "serde_string")]
    trace_path: TracePath,
    /// Base denomination of the relayed fungible token.
    base_denom: BaseDenom,
}

impl PrefixedDenom {
    /// Returns a coin denomination for an ICS20 fungible token in the format
    /// 'ibc/{Hash(trace_path/base_denom)}'.
    pub fn hashed(&self) -> HashedDenom {
        HashedDenom::from(self)
    }

    /// Removes the specified prefix from the trace path if there is a match, otherwise does nothing.
    pub fn remove_trace_prefix(&mut self, prefix: &TracePrefix) {
        self.trace_path.remove_prefix(prefix)
    }

    /// Adds the specified prefix to the trace path.
    pub fn add_trace_prefix(&mut self, prefix: TracePrefix) {
        self.trace_path.add_prefix(prefix)
    }

    /// Returns `Source::Receiver` if the denomination originally came from the receiving chain and
    /// `Source::Sender` otherwise.
    pub fn source_chain(&self, prefix: &TracePrefix) -> Source {
        if self.trace_path.starts_with(prefix) {
            Source::Receiver
        } else {
            Source::Sender
        }
    }
}

impl FromStr for PrefixedDenom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts: Vec<&str> = s.split('/').collect();
        let last_part = parts.pop().expect("split() returned an empty iterator");

        let (base_denom, trace_path) = {
            if last_part == s {
                (BaseDenom::from_str(s)?, TracePath::default())
            } else {
                let base_denom = BaseDenom::from_str(last_part)?;
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

impl TryFrom<RawDenomTrace> for PrefixedDenom {
    type Error = Error;

    fn try_from(value: RawDenomTrace) -> Result<Self, Self::Error> {
        let base_denom = BaseDenom::from_str(&value.base_denom)?;
        let trace_path = TracePath::from_str(&value.path)?;
        Ok(Self {
            trace_path,
            base_denom,
        })
    }
}

impl From<PrefixedDenom> for RawDenomTrace {
    fn from(value: PrefixedDenom) -> Self {
        Self {
            path: value.trace_path.to_string(),
            base_denom: value.base_denom.to_string(),
        }
    }
}

impl From<BaseDenom> for PrefixedDenom {
    fn from(denom: BaseDenom) -> Self {
        Self {
            trace_path: Default::default(),
            base_denom: denom,
        }
    }
}

impl fmt::Display for PrefixedDenom {
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

impl From<&PrefixedDenom> for HashedDenom {
    fn from(value: &PrefixedDenom) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(value.to_string().as_bytes());
        let denom_bytes = hasher.finalize();
        Self(denom_bytes.to_vec())
    }
}

impl fmt::Display for HashedDenom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let denom_hex = String::from_utf8(hex::encode_upper(&self.0)).map_err(|_| fmt::Error)?;
        write!(f, "{}/{}", IBC_DENOM_PREFIX, denom_hex)
    }
}

impl FromStr for HashedDenom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = s.split('/').collect();
        if parts.len() != 2 || parts[1].trim().is_empty() {
            return Err(Error::malformed_hash_denom());
        } else if parts[0] != IBC_DENOM_PREFIX {
            return Err(Error::missing_denom_ibc_prefix());
        }

        let bytes = hex::decode_upper(parts[1]).map_err(Error::parse_hex)?;
        Ok(Self(bytes))
    }
}

/// A type for representing token transfer amounts.
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Display, From, Into)]
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
        let amount = U256::from_str_radix(s, 10).map_err(Error::invalid_amount)?;
        Ok(Self(amount))
    }
}

impl From<u64> for Amount {
    fn from(v: u64) -> Self {
        Self(v.into())
    }
}

/// Coin defines a token with a denomination and an amount.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Coin<D> {
    /// Denomination
    pub denom: D,
    /// Amount
    #[serde(with = "serde_string")]
    pub amount: Amount,
}

impl<D: FromStr> TryFrom<RawCoin> for Coin<D>
where
    Error: From<<D as FromStr>::Err>,
{
    type Error = Error;

    fn try_from(proto: RawCoin) -> Result<Coin<D>, Self::Error> {
        let denom = D::from_str(&proto.denom)?;
        let amount = Amount::from_str(&proto.amount)?;
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
    pub fn amount(&self) -> Amount {
        match self {
            IbcCoin::Hashed(c) => c.amount,
            IbcCoin::Base(c) => c.amount,
        }
    }
}

impl fmt::Display for IbcCoin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IbcCoin::Hashed(coin) => write!(f, "{}-{}", coin.amount, coin.denom),
            IbcCoin::Base(coin) => write!(f, "{}-{}", coin.amount, coin.denom),
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
        if !denom.trace_path.is_empty() {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_denom_validation() -> Result<(), Error> {
        assert!(BaseDenom::from_str("").is_err(), "empty base denom");
        assert!(BaseDenom::from_str("uatom").is_ok(), "valid base denom");
        assert!(PrefixedDenom::from_str("").is_err(), "empty denom trace");
        assert!(
            PrefixedDenom::from_str("transfer/channel-0/").is_err(),
            "empty base denom with trace"
        );
        assert!(PrefixedDenom::from_str("/uatom").is_err(), "empty prefix");
        assert!(PrefixedDenom::from_str("//uatom").is_err(), "empty ids");
        assert!(
            PrefixedDenom::from_str("transfer/").is_err(),
            "single trace"
        );
        assert!(
            PrefixedDenom::from_str("transfer/atom").is_err(),
            "single trace with base denom"
        );
        assert!(
            PrefixedDenom::from_str("transfer/channel-0/uatom").is_ok(),
            "valid single trace info"
        );
        assert!(
            PrefixedDenom::from_str("transfer/channel-0/transfer/channel-1/uatom").is_ok(),
            "valid multiple trace info"
        );
        assert!(
            PrefixedDenom::from_str("(transfer)/channel-0/uatom").is_err(),
            "invalid port"
        );
        assert!(
            PrefixedDenom::from_str("transfer/(channel-0)/uatom").is_err(),
            "invalid channel"
        );

        Ok(())
    }

    #[test]
    fn test_denom_trace() -> Result<(), Error> {
        assert_eq!(
            PrefixedDenom::from_str("transfer/channel-0/uatom")?,
            PrefixedDenom {
                trace_path: "transfer/channel-0".parse()?,
                base_denom: "uatom".parse()?
            },
            "valid single trace info"
        );
        assert_eq!(
            PrefixedDenom::from_str("transfer/channel-0/transfer/channel-1/uatom")?,
            PrefixedDenom {
                trace_path: "transfer/channel-0/transfer/channel-1".parse()?,
                base_denom: "uatom".parse()?
            },
            "valid multiple trace info"
        );

        Ok(())
    }

    #[test]
    fn test_denom_serde() -> Result<(), Error> {
        let dt_str = "transfer/channel-0/uatom";
        let dt = PrefixedDenom::from_str(dt_str)?;
        assert_eq!(dt.to_string(), dt_str, "valid single trace info");

        let dt_str = "transfer/channel-0/transfer/channel-1/uatom";
        let dt = PrefixedDenom::from_str(dt_str)?;
        assert_eq!(dt.to_string(), dt_str, "valid multiple trace info");

        Ok(())
    }

    #[test]
    fn test_trace_path() -> Result<(), Error> {
        assert!(TracePath::from_str("").is_ok(), "empty trace path");
        assert!(
            TracePath::from_str("transfer/uatom").is_err(),
            "invalid trace path: bad ChannelId"
        );
        assert!(
            TracePath::from_str("transfer//uatom").is_err(),
            "malformed trace path: missing ChannelId"
        );
        assert!(
            TracePath::from_str("transfer/channel-0/").is_err(),
            "malformed trace path: trailing delimiter"
        );

        let prefix = TracePrefix::new("transfer".parse().unwrap(), "channel-0".parse().unwrap());
        let mut trace_path = TracePath::from_str("transfer/channel-1")?;

        trace_path.add_prefix(prefix.clone());
        assert_eq!(
            TracePath::from_str("transfer/channel-0/transfer/channel-1")?,
            trace_path
        );

        trace_path.remove_prefix(&prefix);
        assert_eq!(TracePath::from_str("transfer/channel-1")?, trace_path);

        Ok(())
    }

    #[test]
    fn test_ibc_coin_from_prefixed_coin() -> Result<(), Error> {
        let denom_str = "uatom";
        let amount = "1000".parse()?;
        let coin = PrefixedCoin {
            denom: denom_str.parse()?,
            amount,
        };
        assert_eq!(
            IbcCoin::from(coin),
            IbcCoin::Base(BaseCoin {
                denom: denom_str.parse()?,
                amount,
            }),
            "valid base denom"
        );

        let denom_str = "transfer/channel-0/uatom";
        let amount = "1000".parse()?;
        let coin = PrefixedCoin {
            denom: denom_str.parse()?,
            amount,
        };
        assert_eq!(
            IbcCoin::from(coin),
            IbcCoin::Hashed(HashedCoin {
                denom: "ibc/27394FB092D2ECCD56123C74F36E4C1F926001CEADA9CA97EA622B25F41E5EB2"
                    .parse()?,
                amount,
            }),
            "valid hashed denom"
        );

        Ok(())
    }

    #[test]
    fn test_ibc_coin_validation() -> Result<(), Error> {
        struct Test {
            name: &'static str,
            denom: &'static str,
            exp_coin: Option<IbcCoin>,
        }

        let amount = Amount::from_str("1000")?;
        let hashed_denom = "ibc/27394FB092D2ECCD56123C74F36E4C1F926001CEADA9CA97EA622B25F41E5EB2";
        let base_denom_slash = "gamm/pool/1";
        let base_denom_double_slash = "gamm//pool//1";
        let non_ibc_prefixed_denom =
            "notibc/7F1D3FCF4AE79E1554D670D1AD949A9BA4E4A3C76C63093E17E446A46061A7A2";

        let tests: Vec<Test> = vec![
            Test {
                name: "hashed denom",
                denom: hashed_denom,
                exp_coin: Some(IbcCoin::Hashed(HashedCoin {
                    denom: hashed_denom.parse()?,
                    amount,
                })),
            },
            Test {
                name: "base denom with '/'s",
                denom: base_denom_slash,
                exp_coin: Some(IbcCoin::Base(BaseCoin {
                    denom: base_denom_slash.parse()?,
                    amount,
                })),
            },
            Test {
                name: "base denom with '//'s",
                denom: base_denom_double_slash,
                exp_coin: Some(IbcCoin::Base(BaseCoin {
                    denom: base_denom_double_slash.parse()?,
                    amount,
                })),
            },
            Test {
                name: "non-ibc prefix with hash",
                denom: non_ibc_prefixed_denom,
                exp_coin: Some(IbcCoin::Base(BaseCoin {
                    denom: non_ibc_prefixed_denom.parse()?,
                    amount,
                })),
            },
            Test {
                name: "empty denom",
                denom: "",
                exp_coin: None,
            },
            Test {
                name: "'ibc' denom",
                denom: "ibc",
                exp_coin: None,
            },
            Test {
                name: "'ibc/' denom",
                denom: "ibc/",
                exp_coin: None,
            },
            Test {
                name: "invalid hashed denom",
                denom: "ibc/!@#$!@#",
                exp_coin: None,
            },
        ];

        for test in tests {
            let coin = RawCoin {
                denom: test.denom.to_string(),
                amount: amount.to_string(),
            };

            if let Some(exp_coin) = test.exp_coin {
                assert_eq!(IbcCoin::try_from(coin)?, exp_coin, "{}", test.name);
            } else {
                assert!(IbcCoin::try_from(coin).is_err(), "{}", test.name)
            }
        }

        Ok(())
    }
}
