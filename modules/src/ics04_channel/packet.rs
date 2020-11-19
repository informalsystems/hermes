use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;

use crate::ics04_channel::error::Kind;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::Height;

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
                .ok_or(Kind::MissingHeight)?
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

#[cfg(test)]
pub mod test_utils {
    use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    /// Returns a dummy `RawPacket`, for testing only!
    pub fn get_dummy_raw_packet(timeout_height: u64) -> RawPacket {
        RawPacket {
            sequence: 0,
            source_port: "sourceportid".to_string(),
            source_channel: "srchannelid".to_string(),
            destination_port: "destinationport".to_string(),
            destination_channel: "dstchannelid".to_string(),
            data: vec![],
            timeout_height: Some(RawHeight {
                version_number: 1,
                version_height: timeout_height,
            }),
            timeout_timestamp: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;

    use crate::ics04_channel::packet::test_utils::get_dummy_raw_packet;
    use crate::ics04_channel::packet::Packet;

    #[test]
    fn packet_try_from_raw() {
        struct Test {
            name: String,
            raw: RawPacket,
            want_pass: bool,
        }

        let proof_height = 10;
        let default_raw_msg = get_dummy_raw_packet(proof_height);

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true
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
                    source_port: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
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
                    destination_port: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Src channel validation: correct".to_string(),
                raw: RawPacket {
                    source_channel: "srcchannelp34".to_string(),
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
                    source_channel: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Dst channel validation: correct".to_string(),
                raw: RawPacket {
                    destination_channel: "dstchannelp34".to_string(),
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
                    destination_channel: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
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
        let raw = get_dummy_raw_packet(15);
        let msg = Packet::try_from(raw.clone()).unwrap();
        let raw_back = RawPacket::from(msg.clone());
        let msg_back = Packet::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
