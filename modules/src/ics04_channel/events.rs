//! Types for the IBC events emitted from Tendermint Websocket by the channels module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics02_client::height::Height;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};
use tendermint::block;

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenInit {
    pub height: block::Height,
    pub port_id: PortId,
    pub connection_id: ConnectionId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: ChannelId,
}

impl TryFrom<RawObject> for OpenInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenInit {
            height: obj.height,
            port_id: attribute!(obj, "channel_open_init.port_id"),
            connection_id: attribute!(obj, "channel_open_init.connection_id"),
            channel_id: attribute!(obj, "channel_open_init.channel_id"),
            counterparty_port_id: attribute!(obj, "channel_open_init.counterparty_port_id"),
            counterparty_channel_id: attribute!(obj, "channel_open_init.counterparty_channel_id"),
        })
    }
}

impl From<OpenInit> for IBCEvent {
    fn from(v: OpenInit) -> Self {
        IBCEvent::OpenInitChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenTry {
    pub height: block::Height,
    pub port_id: PortId,
    pub connection_id: ConnectionId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: ChannelId,
}

impl TryFrom<RawObject> for OpenTry {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenTry {
            height: obj.height,
            port_id: attribute!(obj, "channel_open_try.port_id"),
            connection_id: attribute!(obj, "channel_open_try.connection_id"),
            channel_id: attribute!(obj, "channel_open_try.channel_id"),
            counterparty_port_id: attribute!(obj, "channel_open_try.counterparty_port_id"),
            counterparty_channel_id: attribute!(obj, "channel_open_try.counterparty_channel_id"),
        })
    }
}

impl From<OpenTry> for IBCEvent {
    fn from(v: OpenTry) -> Self {
        IBCEvent::OpenTryChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenAck {
    pub height: block::Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl TryFrom<RawObject> for OpenAck {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenAck {
            height: obj.height,
            port_id: attribute!(obj, "channel_open_ack.port_id"),
            channel_id: attribute!(obj, "channel_open_ack.channel_id"),
        })
    }
}

impl From<OpenAck> for IBCEvent {
    fn from(v: OpenAck) -> Self {
        IBCEvent::OpenAckChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenConfirm {
    pub height: block::Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl TryFrom<RawObject> for OpenConfirm {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenConfirm {
            height: obj.height,
            port_id: attribute!(obj, "channel_open_confirm.port_id"),
            channel_id: attribute!(obj, "channel_open_confirm.channel_id"),
        })
    }
}

impl From<OpenConfirm> for IBCEvent {
    fn from(v: OpenConfirm) -> Self {
        IBCEvent::OpenConfirmChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CloseInit {
    pub height: block::Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl TryFrom<RawObject> for CloseInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CloseInit {
            height: obj.height,
            port_id: attribute!(obj, "channel_close_init.port_id"),
            channel_id: attribute!(obj, "channel_close_init.channel_id"),
        })
    }
}

impl From<CloseInit> for IBCEvent {
    fn from(v: CloseInit) -> Self {
        IBCEvent::CloseInitChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CloseConfirm {
    pub height: block::Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl TryFrom<RawObject> for CloseConfirm {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CloseConfirm {
            height: obj.height,
            port_id: attribute!(obj, "channel_close_confirm.port_id"),
            channel_id: attribute!(obj, "channel_close_confirm.channel_id"),
        })
    }
}

impl From<CloseConfirm> for IBCEvent {
    fn from(v: CloseConfirm) -> Self {
        IBCEvent::CloseConfirmChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct PacketEnvelope {
    pub height: block::Height,
    pub packet_src_port: PortId,
    pub packet_src_channel: ChannelId,
    pub packet_dst_port: PortId,
    pub packet_dst_channel: ChannelId,
    pub packet_sequence: u64,
    pub packet_timeout_height: Height,
    pub packet_timeout_stamp: u64,
}

impl TryFrom<RawObject> for PacketEnvelope {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height_str: String = attribute!(obj, "send_packet.packet_timeout_height");
        Ok(PacketEnvelope {
            height: obj.height,
            packet_src_port: attribute!(obj, "send_packet.packet_src_port"),
            packet_src_channel: attribute!(obj, "send_packet.packet_src_channel"),
            packet_dst_port: attribute!(obj, "send_packet.packet_dst_port"),
            packet_dst_channel: attribute!(obj, "send_packet.packet_dst_channel"),
            packet_sequence: attribute!(obj, "send_packet.packet_sequence"),
            packet_timeout_height: height_str.try_into()?,
            packet_timeout_stamp: attribute!(obj, "send_packet.packet_timeout_timestamp"),
        })
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct SendPacket {
    pub envelope: PacketEnvelope,
    pub data: Vec<u8>,
}

impl TryFrom<RawObject> for SendPacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let data_str: String = attribute!(obj, "send_packet.packet_data");
        Ok(SendPacket {
            envelope: PacketEnvelope::try_from(obj)?,
            data: Vec::from(data_str.as_str().as_bytes()),
        })
    }
}

impl From<SendPacket> for IBCEvent {
    fn from(v: SendPacket) -> Self {
        IBCEvent::SendPacketChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ReceivePacket {
    pub height: block::Height,
    pub packet_src_port: PortId,
    pub packet_src_channel: ChannelId,
    pub packet_dst_port: PortId,
    pub packet_dst_channel: ChannelId,
    pub packet_sequence: u64,
    pub packet_timeout_height: String,
    pub packet_timeout_stamp: u64,
}

impl TryFrom<RawObject> for ReceivePacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(ReceivePacket {
            height: obj.height,
            packet_src_port: attribute!(obj, "recv_packet.packet_src_port"),
            packet_src_channel: attribute!(obj, "recv_packet.packet_src_channel"),
            packet_dst_port: attribute!(obj, "recv_packet.packet_dst_port"),
            packet_dst_channel: attribute!(obj, "recv_packet.packet_dst_channel"),
            packet_sequence: attribute!(obj, "recv_packet.packet_sequence"),
            packet_timeout_height: attribute!(obj, "recv_packet.packet_timeout_height"),
            packet_timeout_stamp: attribute!(obj, "recv_packet.packet_timeout_timestamp"),
        })
    }
}

impl From<ReceivePacket> for IBCEvent {
    fn from(v: ReceivePacket) -> Self {
        IBCEvent::ReceivePacketChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct AcknowledgePacket {
    pub height: block::Height,
    pub packet_src_port: PortId,
    pub packet_src_channel: ChannelId,
    pub packet_dst_port: PortId,
    pub packet_dst_channel: ChannelId,
    pub packet_sequence: u64,
    pub packet_timeout_height: u64,
    pub packet_timeout_stamp: u64,
}

impl TryFrom<RawObject> for AcknowledgePacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(AcknowledgePacket {
            height: obj.height,
            packet_src_port: attribute!(obj, "acknowledge_packet.packet_src_port"),
            packet_src_channel: attribute!(obj, "acknowledge_packet.packet_src_channel"),
            packet_dst_port: attribute!(obj, "acknowledge_packet.packet_dst_port"),
            packet_dst_channel: attribute!(obj, "acknowledge_packet.packet_dst_channel"),
            packet_sequence: attribute!(obj, "acknowledge_packet.packet_sequence"),
            packet_timeout_height: attribute!(obj, "acknowledge_packet.packet_timeout_height"),
            packet_timeout_stamp: attribute!(obj, "acknowledge_packet.packet_timeout_timestamp"),
        })
    }
}

impl From<AcknowledgePacket> for IBCEvent {
    fn from(v: AcknowledgePacket) -> Self {
        IBCEvent::AcknowledgePacketChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CleanupPacket {
    pub height: block::Height,
    pub packet_src_port: PortId,
    pub packet_src_channel: ChannelId,
    pub packet_dst_port: PortId,
    pub packet_dst_channel: ChannelId,
    pub packet_sequence: u64,
    pub packet_timeout_height: u64,
    pub packet_timeout_stamp: u64,
}

impl TryFrom<RawObject> for CleanupPacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CleanupPacket {
            height: obj.height,
            packet_src_port: attribute!(obj, "cleanup_packet.packet_src_port"),
            packet_src_channel: attribute!(obj, "cleanup_packet.packet_src_channel"),
            packet_dst_port: attribute!(obj, "cleanup_packet.packet_dst_port"),
            packet_dst_channel: attribute!(obj, "cleanup_packet.packet_dst_channel"),
            packet_sequence: attribute!(obj, "cleanup_packet.packet_sequence"),
            packet_timeout_height: attribute!(obj, "cleanup_packet.packet_timeout_height"),
            packet_timeout_stamp: attribute!(obj, "cleanup_packet.packet_timeout_timestamp"),
        })
    }
}

impl From<CleanupPacket> for IBCEvent {
    fn from(v: CleanupPacket) -> Self {
        IBCEvent::CleanupPacketChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct TimeoutPacket {
    pub height: block::Height,
    pub packet_src_port: PortId,
    pub packet_src_channel: ChannelId,
    pub packet_dst_port: PortId,
    pub packet_dst_channel: ChannelId,
    pub packet_sequence: u64,
    pub packet_timeout_height: u64,
    pub packet_timeout_stamp: u64,
}

impl TryFrom<RawObject> for TimeoutPacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(TimeoutPacket {
            height: obj.height,
            packet_src_port: attribute!(obj, "timeout_packet.packet_src_port"),
            packet_src_channel: attribute!(obj, "timeout_packet.packet_src_channel"),
            packet_dst_port: attribute!(obj, "timeout_packet.packet_dst_port"),
            packet_dst_channel: attribute!(obj, "timeout_packet.packet_dst_channel"),
            packet_sequence: attribute!(obj, "timeout_packet.packet_sequence"),
            packet_timeout_height: attribute!(obj, "timeout_packet.packet_timeout_height"),
            packet_timeout_stamp: attribute!(obj, "timeout_packet.packet_timeout_timestamp"),
        })
    }
}

impl From<TimeoutPacket> for IBCEvent {
    fn from(v: TimeoutPacket) -> Self {
        IBCEvent::TimeoutPacketChannel(v)
    }
}
