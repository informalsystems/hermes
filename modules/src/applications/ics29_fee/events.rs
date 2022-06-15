use core::str::FromStr;
use tendermint::abci::tag::Tag;

use super::error::Error;
use crate::applications::transfer::coin::RawCoin;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

pub struct IncentivizedPacketEvent {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
    pub total_recv_fee: Vec<RawCoin>,
    pub total_ack_fee: Vec<RawCoin>,
    pub total_timeout_fee: Vec<RawCoin>,
}

fn find_value(key: &str, entries: &[Tag]) -> Result<String, Error> {
    entries
        .iter()
        .find_map(|entry| {
            if entry.key.as_ref() == key {
                Some(entry.value.to_string())
            } else {
                None
            }
        })
        .ok_or_else(|| Error::event_attribute_not_found(key.to_string()))
}

impl TryFrom<Vec<Tag>> for IncentivizedPacketEvent {
    type Error = Error;

    fn try_from(entries: Vec<Tag>) -> Result<Self, Error> {
        let port_id_str = find_value("port_id", &entries)?;
        let channel_id_str = find_value("channel_id", &entries)?;
        let sequence_str = find_value("packet_sequence", &entries)?;
        let recv_fee_str = find_value("recv_fee", &entries)?;
        let ack_fee_str = find_value("ack_fee", &entries)?;
        let timeout_fee_str = find_value("timeout_fee", &entries)?;

        let port_id = PortId::from_str(&port_id_str).map_err(Error::ics24)?;

        let channel_id = ChannelId::from_str(&channel_id_str).map_err(Error::ics24)?;

        let sequence = Sequence::from_str(&sequence_str).map_err(Error::channel)?;

        let total_recv_fee = RawCoin::from_string_list(&recv_fee_str).map_err(Error::transfer)?;

        let total_ack_fee = RawCoin::from_string_list(&ack_fee_str).map_err(Error::transfer)?;

        let total_timeout_fee =
            RawCoin::from_string_list(&timeout_fee_str).map_err(Error::transfer)?;

        Ok(IncentivizedPacketEvent {
            port_id,
            channel_id,
            sequence,
            total_recv_fee,
            total_ack_fee,
            total_timeout_fee,
        })
    }
}
