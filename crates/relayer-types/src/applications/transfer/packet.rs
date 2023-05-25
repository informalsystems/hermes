use alloc::string::{String, ToString};
use core::convert::TryFrom;
use core::str::FromStr;

use ibc_proto::ibc::applications::transfer::v2::FungibleTokenPacketData as RawPacketData;
use serde::{Deserialize, Serialize};

use super::error::Error;
use super::{Amount, PrefixedCoin, PrefixedDenom};
use crate::signer::Signer;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RawPacketData", into = "RawPacketData")]
pub struct PacketData {
    pub token: PrefixedCoin,
    pub sender: Signer,
    pub receiver: Signer,
    pub memo: Option<String>,
}

impl TryFrom<RawPacketData> for PacketData {
    type Error = Error;

    fn try_from(raw_pkt_data: RawPacketData) -> Result<Self, Self::Error> {
        // This denom may be prefixed or unprefixed.
        let denom = PrefixedDenom::from_str(&raw_pkt_data.denom)?;
        let amount = Amount::from_str(&raw_pkt_data.amount)?;
        let memo = Some(raw_pkt_data.memo).filter(|m| !m.is_empty());
        Ok(Self {
            token: PrefixedCoin { denom, amount },
            sender: raw_pkt_data.sender.parse().map_err(Error::signer)?,
            receiver: raw_pkt_data.receiver.parse().map_err(Error::signer)?,
            memo,
        })
    }
}

impl From<PacketData> for RawPacketData {
    fn from(pkt_data: PacketData) -> Self {
        let memo = pkt_data.memo.unwrap_or_default();
        Self {
            denom: pkt_data.token.denom.to_string(),
            amount: pkt_data.token.amount.to_string(),
            sender: pkt_data.sender.to_string(),
            receiver: pkt_data.receiver.to_string(),
            memo,
        }
    }
}
