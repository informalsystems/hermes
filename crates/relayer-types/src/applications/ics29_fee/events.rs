use core::fmt::Display;
use core::str::FromStr;
use itertools::Itertools;
use serde_derive::{Deserialize, Serialize};
use tendermint::abci;

use super::error::Error;
use crate::applications::transfer::coin::RawCoin;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::events::IbcEventType;
use crate::prelude::*;
use crate::signer::Signer;

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub struct IncentivizedPacket {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
    pub total_recv_fee: Vec<RawCoin>,
    pub total_ack_fee: Vec<RawCoin>,
    pub total_timeout_fee: Vec<RawCoin>,
}

fn find_value<'a>(key: &str, entries: &'a [abci::EventAttribute]) -> Result<&'a str, Error> {
    entries
        .iter()
        .find_map(|entry| {
            if entry.key == key {
                Some(entry.value.as_str())
            } else {
                None
            }
        })
        .ok_or_else(|| Error::event_attribute_not_found(key.to_owned()))
}

impl From<IncentivizedPacket> for abci::Event {
    fn from(event: IncentivizedPacket) -> Self {
        let attributes = vec![
            ("port_id", event.port_id.as_str()).into(),
            ("channel_id", event.channel_id.as_str()).into(),
            ("packet_sequence", &event.sequence.to_string()).into(),
            ("recv_fee", &event.total_recv_fee.iter().join(",")).into(),
            ("ack_fee", &event.total_ack_fee.iter().join(",")).into(),
            ("timeout_fee", &event.total_timeout_fee.iter().join(",")).into(),
        ];

        Self {
            kind: IbcEventType::IncentivizedPacket.as_str().to_owned(),
            attributes,
        }
    }
}

impl<'a> TryFrom<&'a [abci::EventAttribute]> for IncentivizedPacket {
    type Error = Error;

    fn try_from(entries: &'a [abci::EventAttribute]) -> Result<Self, Error> {
        let port_id_str = find_value("port_id", entries)?;
        let channel_id_str = find_value("channel_id", entries)?;
        let sequence_str = find_value("packet_sequence", entries)?;
        let recv_fee_str = find_value("recv_fee", entries)?;
        let ack_fee_str = find_value("ack_fee", entries)?;
        let timeout_fee_str = find_value("timeout_fee", entries)?;

        let port_id = PortId::from_str(port_id_str).map_err(Error::ics24)?;

        let channel_id = ChannelId::from_str(channel_id_str).map_err(Error::ics24)?;

        let sequence = Sequence::from_str(sequence_str).map_err(Error::channel)?;

        let total_recv_fee = RawCoin::from_string_list(recv_fee_str).map_err(Error::transfer)?;

        let total_ack_fee = RawCoin::from_string_list(ack_fee_str).map_err(Error::transfer)?;

        let total_timeout_fee =
            RawCoin::from_string_list(timeout_fee_str).map_err(Error::transfer)?;

        Ok(IncentivizedPacket {
            port_id,
            channel_id,
            sequence,
            total_recv_fee,
            total_ack_fee,
            total_timeout_fee,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub enum DistributionType {
    Reward,
    Refund,
}

impl Display for DistributionType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DistributionType::Reward => write!(f, "reward"),
            DistributionType::Refund => write!(f, "refund"),
        }
    }
}

impl TryFrom<&str> for DistributionType {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "reward" => Ok(DistributionType::Reward),
            "refund" => Ok(DistributionType::Refund),
            _ => Err(Error::empty_fee()),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub struct DistributeFeePacket {
    pub receiver: Signer,
    pub fee: RawCoin,
    pub distribution_type: DistributionType,
}

impl From<DistributeFeePacket> for abci::Event {
    fn from(event: DistributeFeePacket) -> Self {
        let attributes = vec![
            ("receiver", event.receiver.to_string()).into(),
            ("fee", event.fee.denom.as_str()).into(),
            ("distribution_type", event.distribution_type.to_string()).into(),
        ];

        Self {
            kind: IbcEventType::DistributionFee.as_str().to_owned(),
            attributes,
        }
    }
}

impl<'a> TryFrom<&'a [abci::EventAttribute]> for DistributeFeePacket {
    type Error = Error;

    fn try_from(entries: &'a [abci::EventAttribute]) -> Result<Self, Error> {
        let receiver_str = find_value("receiver", entries)?;
        let fee_str = find_value("fee", entries)?;
        let distribution_type_str = find_value("distribution_type", entries)?;

        let receiver = Signer::from_str(receiver_str).map_err(Error::signer)?;

        let fee = RawCoin::from_str(fee_str).map_err(Error::transfer)?;

        let distribution_type = DistributionType::try_from(distribution_type_str)?;

        Ok(DistributeFeePacket {
            receiver,
            fee,
            distribution_type,
        })
    }
}
