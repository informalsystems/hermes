use crate::prelude::*;

use core::str::FromStr;

use serde_derive::{Deserialize, Serialize};

use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;

use crate::core::ics04_channel::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::events::{extract_attribute, Error as EventError, RawObject};
use crate::timestamp::{Expiry::Expired, Timestamp};
use crate::Height;

use super::handler::{
    acknowledgement::AckPacketResult, recv_packet::RecvPacketResult, send_packet::SendPacketResult,
    timeout::TimeoutPacketResult, write_acknowledgement::WriteAckPacketResult,
};

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PacketMsgType {
    Recv,
    Ack,
    TimeoutUnordered,
    TimeoutOrdered,
    TimeoutOnClose,
}

#[derive(Clone, Debug)]
pub enum PacketResult {
    Send(SendPacketResult),
    Recv(RecvPacketResult),
    WriteAck(WriteAckPacketResult),
    Ack(AckPacketResult),
    Timeout(TimeoutPacketResult),
}

#[derive(Clone, Debug)]
pub enum Receipt {
    Ok,
}

impl core::fmt::Display for PacketMsgType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PacketMsgType::Recv => write!(f, "(PacketMsgType::Recv)"),
            PacketMsgType::Ack => write!(f, "(PacketMsgType::Ack)"),
            PacketMsgType::TimeoutUnordered => write!(f, "(PacketMsgType::TimeoutUnordered)"),
            PacketMsgType::TimeoutOrdered => write!(f, "(PacketMsgType::TimeoutOrdered)"),
            PacketMsgType::TimeoutOnClose => write!(f, "(PacketMsgType::TimeoutOnClose)"),
        }
    }
}

/// The sequence number of a packet enforces ordering among packets from the same source.
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize,
)]
pub struct Sequence(u64);

impl FromStr for Sequence {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s.parse::<u64>().map_err(|e| {
            Error::invalid_string_as_sequence(s.to_string(), e)
        })?))
    }
}

impl Sequence {
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    pub fn increment(&self) -> Sequence {
        Sequence(self.0 + 1)
    }
}

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

impl core::fmt::Display for Sequence {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Default, Hash, PartialEq, Eq, Deserialize, Serialize)]
pub struct Packet {
    pub sequence: Sequence,
    pub source_port: PortId,
    pub source_channel: ChannelId,
    pub destination_port: PortId,
    pub destination_channel: ChannelId,
    #[serde(serialize_with = "crate::serializers::ser_hex_upper")]
    pub data: Vec<u8>,
    pub timeout_height: Height,
    pub timeout_timestamp: Timestamp,
}

struct PacketData<'a>(&'a [u8]);

impl<'a> core::fmt::Debug for PacketData<'a> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(formatter, "{:?}", self.0)
    }
}

impl core::fmt::Debug for Packet {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        // Remember: if you alter the definition of `Packet`,
        // 1. update the formatter debug struct builder calls (return object of
        //    this function)
        // 2. update this destructuring assignment accordingly
        let Packet {
            sequence: _,
            source_port: _,
            source_channel: _,
            destination_port: _,
            destination_channel: _,
            data,
            timeout_height: _,
            timeout_timestamp: _,
        } = self;
        let data_wrapper = PacketData(data);

        formatter
            .debug_struct("Packet")
            .field("sequence", &self.sequence)
            .field("source_port", &self.source_port)
            .field("source_channel", &self.source_channel)
            .field("destination_port", &self.destination_port)
            .field("destination_channel", &self.destination_channel)
            .field("data", &data_wrapper)
            .field("timeout_height", &self.timeout_height)
            .field("timeout_timestamp", &self.timeout_timestamp)
            .finish()
    }
}

impl Packet {
    /// Checks whether a packet from a
    /// [`SendPacket`](crate::core::ics04_channel::events::SendPacket)
    /// event is timed-out relative to the current state of the
    /// destination chain.
    ///
    /// Checks both for time-out relative to the destination chain's
    /// current timestamp `dst_chain_ts` as well as relative to
    /// the height `dst_chain_height`.
    ///
    /// Note: a timed-out packet should result in a
    /// [`MsgTimeout`](crate::core::ics04_channel::msgs::timeout::MsgTimeout),
    /// instead of the common-case where it results in
    /// [`MsgRecvPacket`](crate::core::ics04_channel::msgs::recv_packet::MsgRecvPacket).
    pub fn timed_out(&self, dst_chain_ts: &Timestamp, dst_chain_height: Height) -> bool {
        (self.timeout_height != Height::zero() && self.timeout_height < dst_chain_height)
            || (self.timeout_timestamp != Timestamp::none()
                && dst_chain_ts.check_expiry(&self.timeout_timestamp) == Expired)
    }
}

/// Custom debug output to omit the packet data
impl core::fmt::Display for Packet {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "seq:{}, path:{}/{}->{}/{}, toh:{}, tos:{})",
            self.sequence,
            self.source_channel,
            self.source_port,
            self.destination_channel,
            self.destination_port,
            self.timeout_height,
            self.timeout_timestamp
        )
    }
}

impl TryFrom<RawPacket> for Packet {
    type Error = Error;

    fn try_from(raw_pkt: RawPacket) -> Result<Self, Self::Error> {
        if Sequence::from(raw_pkt.sequence).is_zero() {
            return Err(Error::zero_packet_sequence());
        }
        let packet_timeout_height: Height = raw_pkt
            .timeout_height
            .ok_or_else(Error::missing_height)?
            .into();

        if packet_timeout_height.is_zero() && raw_pkt.timeout_timestamp == 0 {
            return Err(Error::zero_packet_timeout());
        }
        if raw_pkt.data.is_empty() {
            return Err(Error::zero_packet_data());
        }

        let timeout_timestamp = Timestamp::from_nanoseconds(raw_pkt.timeout_timestamp)
            .map_err(Error::invalid_packet_timestamp)?;

        Ok(Packet {
            sequence: Sequence::from(raw_pkt.sequence),
            source_port: raw_pkt.source_port.parse().map_err(Error::identifier)?,
            source_channel: raw_pkt.source_channel.parse().map_err(Error::identifier)?,
            destination_port: raw_pkt
                .destination_port
                .parse()
                .map_err(Error::identifier)?,
            destination_channel: raw_pkt
                .destination_channel
                .parse()
                .map_err(Error::identifier)?,
            data: raw_pkt.data,
            timeout_height: packet_timeout_height,
            timeout_timestamp,
        })
    }
}

impl TryFrom<RawObject<'_>> for Packet {
    type Error = EventError;
    fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
        Ok(Packet {
            sequence: extract_attribute(&obj, &format!("{}.packet_sequence", obj.action))?
                .parse()
                .map_err(EventError::channel)?,
            source_port: extract_attribute(&obj, &format!("{}.packet_src_port", obj.action))?
                .parse()
                .map_err(EventError::parse)?,
            source_channel: extract_attribute(&obj, &format!("{}.packet_src_channel", obj.action))?
                .parse()
                .map_err(EventError::parse)?,
            destination_port: extract_attribute(&obj, &format!("{}.packet_dst_port", obj.action))?
                .parse()
                .map_err(EventError::parse)?,
            destination_channel: extract_attribute(
                &obj,
                &format!("{}.packet_dst_channel", obj.action),
            )?
            .parse()
            .map_err(EventError::parse)?,
            data: vec![],
            timeout_height: extract_attribute(
                &obj,
                &format!("{}.packet_timeout_height", obj.action),
            )?
            .parse()
            .map_err(EventError::height)?,
            timeout_timestamp: extract_attribute(
                &obj,
                &format!("{}.packet_timeout_timestamp", obj.action),
            )?
            .parse()
            .map_err(EventError::timestamp)?,
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
            timeout_timestamp: packet.timeout_timestamp.nanoseconds(),
        }
    }
}

#[cfg(test)]
pub mod test_utils {
    use crate::prelude::*;
    use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics24_host::identifier::{ChannelId, PortId};

    /// Returns a dummy `RawPacket`, for testing only!
    pub fn get_dummy_raw_packet(timeout_height: u64, timeout_timestamp: u64) -> RawPacket {
        RawPacket {
            sequence: 1,
            source_port: PortId::default().to_string(),
            source_channel: ChannelId::default().to_string(),
            destination_port: PortId::default().to_string(),
            destination_channel: ChannelId::default().to_string(),
            data: vec![0],
            timeout_height: Some(RawHeight {
                revision_number: 0,
                revision_height: timeout_height,
            }),
            timeout_timestamp,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;

    use crate::core::ics04_channel::packet::test_utils::get_dummy_raw_packet;
    use crate::core::ics04_channel::packet::Packet;

    #[test]
    fn packet_try_from_raw() {
        struct Test {
            name: String,
            raw: RawPacket,
            want_pass: bool,
        }

        let proof_height = 10;
        let default_raw_msg = get_dummy_raw_packet(proof_height, 0);

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Src port validation: correct".to_string(),
                raw: RawPacket {
                    source_port: "srcportp34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad src port, name too short".to_string(),
                raw: RawPacket {
                    source_port: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad src port, name too long".to_string(),
                raw: RawPacket {
                    source_port: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstuabcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Dst port validation: correct".to_string(),
                raw: RawPacket {
                    destination_port: "destportsrcp34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad dst port, name too short".to_string(),
                raw: RawPacket {
                    destination_port: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad dst port, name too long".to_string(),
                raw: RawPacket {
                    destination_port: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstuabcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfas".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Src channel validation: correct".to_string(),
                raw: RawPacket {
                    source_channel: "channel-1".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad src channel, name too short".to_string(),
                raw: RawPacket {
                    source_channel: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad src channel, name too long".to_string(),
                raw: RawPacket {
                    source_channel: "channel-12839128379182739812739879".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Dst channel validation: correct".to_string(),
                raw: RawPacket {
                    destination_channel: "channel-34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad dst channel, name too short".to_string(),
                raw: RawPacket {
                    destination_channel: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad dst channel, name too long".to_string(),
                raw: RawPacket {
                    destination_channel: "channel-12839128379182739812739879".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing timeout height".to_string(),
                raw: RawPacket {
                    timeout_height: None,
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ];

        for test in tests {
            let res_msg = Packet::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res_msg.is_ok(),
                "Packet::try_from failed for test {}, \nraw packet {:?} with error {:?}",
                test.name,
                test.raw,
                res_msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_packet(15, 0);
        let msg = Packet::try_from(raw.clone()).unwrap();
        let raw_back = RawPacket::from(msg.clone());
        let msg_back = Packet::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
