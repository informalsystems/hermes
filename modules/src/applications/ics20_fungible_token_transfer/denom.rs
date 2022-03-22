#![allow(unused)]

use core::convert::AsRef;
use core::fmt;
use core::ops::{Add, AddAssign};
use core::str::FromStr;

use ibc_proto::cosmos::base::v1beta1::Coin as RawCoin;
use ibc_proto::ibc::applications::transfer::v1::DenomTrace as RawDenomTrace;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use super::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

/// Base denomination type
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Denom(String);

impl AsRef<str> for Denom {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

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

impl fmt::Display for Denom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug)]
struct TracePrefix {
    port_id: PortId,
    channel_id: ChannelId,
}

impl fmt::Display for TracePrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.port_id, self.channel_id)
    }
}

#[derive(Clone, Debug, Default)]
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

impl From<Vec<TracePrefix>> for TracePath {
    fn from(v: Vec<TracePrefix>) -> Self {
        Self(v)
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
#[derive(Clone, Debug)]
pub struct DenomTrace {
    /// A series of `{port-id}/{channel-id}`s for tracing the source of the token.
    trace_path: TracePath,
    /// Base denomination of the relayed fungible token.
    base_denom: Denom,
}

impl DenomTrace {
    /// Returns the full denom path
    pub fn get_full_denom_path(&self) -> String {
        todo!()
    }

    /// Returns a coin denomination for an ICS20 fungible token in the format
    /// 'ibc/trace_path/base_denom'. If the trace is empty, it will return the base denomination.
    pub fn ibc_denom(&self) -> String {
        todo!()
    }

    /// Returns the prefix for this trace
    pub fn get_prefix(&self) -> String {
        todo!()
    }

    /// Returns true iff this path has the specified prefix
    pub fn has_prefix(&self, _prefix: &str) -> bool {
        todo!()
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

pub fn derive_ibc_denom(
    port_id: &PortId,
    channel_id: &ChannelId,
    denom: &str,
) -> Result<String, Error> {
    let transfer_path = format!("{}/{}/{}", port_id, channel_id, denom);
    derive_ibc_denom_with_path(&transfer_path)
}

/// Derive the transferred token denomination using
/// <https://github.com/cosmos/ibc-go/blob/main/docs/architecture/adr-001-coin-source-tracing.md>
pub fn derive_ibc_denom_with_path(transfer_path: &str) -> Result<String, Error> {
    let mut hasher = Sha256::new();
    hasher.update(transfer_path.as_bytes());

    let denom_bytes = hasher.finalize();
    let denom_hex = String::from_utf8(hex::encode_upper(denom_bytes)).map_err(Error::utf8)?;

    Ok(format!("ibc/{}", denom_hex))
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Decimal(u64);

impl FromStr for Decimal {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Add for Decimal {
    type Output = Decimal;

    fn add(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl AddAssign for Decimal {
    fn add_assign(&mut self, _rhs: Decimal) {
        todo!()
    }
}

/// Coin defines a token with a denomination and an amount.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Coin {
    /// Denomination
    pub denom: Denom,
    /// Amount
    pub amount: Decimal,
}

impl TryFrom<RawCoin> for Coin {
    type Error = ();

    fn try_from(_proto: RawCoin) -> Result<Coin, Self::Error> {
        todo!()
    }
}

impl From<Coin> for RawCoin {
    fn from(_coin: Coin) -> RawCoin {
        todo!()
    }
}
