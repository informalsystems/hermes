use core::convert::TryFrom;
use core::str::FromStr;
use ibc_proto::ibc::core::channel::v1::PacketId as ProtoPacketId;

use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, PortId};

#[derive(Debug, Clone)]
pub struct PacketId {
    pub channel_id: ChannelId,
    pub port_id: PortId,
    pub sequence: Sequence,
}

impl TryFrom<ProtoPacketId> for PacketId {
    type Error = Error;

    fn try_from(packet_id: ProtoPacketId) -> Result<Self, Error> {
        let channel_id = ChannelId::from_str(&packet_id.channel_id).map_err(Error::identifier)?;

        let port_id = PortId::from_str(&packet_id.port_id).map_err(Error::identifier)?;

        let sequence = Sequence::from(packet_id.sequence);

        Ok(PacketId {
            channel_id,
            port_id,
            sequence,
        })
    }
}
