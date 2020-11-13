use crate::ics04_channel::error::Kind;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::Height;

use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;
use std::convert::{TryFrom, TryInto};

/// The sequence number of a packet enforces ordering among packets from the same source.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sequence(u64);

impl From<u64> for Sequence {
    fn from(seq: u64) -> Self {
        Sequence(seq)
    }
}

impl From<Sequence> for u64 {
    fn from(s: Sequence) -> u64 {
        s.0
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Packet {
    sequence: Sequence,
    source_port: PortId,
    source_channel: ChannelId,
    destination_port: PortId,
    destination_channel: ChannelId,
    data: Vec<u8>,
    timeout_height: Height,
    timeout_timestamp: u64,
}

impl TryFrom<RawPacket> for Packet {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_pkt: RawPacket) -> Result<Self, Self::Error> {
        Ok(Packet {
            sequence: Sequence::from(raw_pkt.sequence),
            source_port: raw_pkt
                .source_port
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            source_channel: raw_pkt
                .source_channel
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            destination_port: raw_pkt
                .destination_port
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            destination_channel: raw_pkt
                .destination_channel
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            data: raw_pkt.data,
            timeout_height: raw_pkt
                .timeout_height
                .ok_or_else(|| Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidTimeoutHeight.context(e))?,
            timeout_timestamp: raw_pkt.timeout_timestamp,
        })
    }
}

impl From<Packet> for RawPacket {
    fn from(packet: Packet) -> Self {
        RawPacket {
            sequence: packet.sequence.0,
            source_port: packet.source_port.to_string(),
            source_channel: packet.source_channel.to_string(),
            destination_port: packet.destination_port.to_string(),
            destination_channel: packet.destination_channel.to_string(),
            data: packet.data,
            timeout_height: Some(packet.timeout_height.into()),
            timeout_timestamp: packet.timeout_timestamp,
        }
    }
}
