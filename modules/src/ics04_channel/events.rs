//! Types for the IBC events emitted from Tendermint Websocket by the channels module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics04_channel::packet::Packet;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};
use tendermint::block;
use std::collections::HashSet;
use std::iter::FromIterator;

pub const SEND_PACKET: &str = "send_packet";
pub const RECV_PACKET: &str = "recv_packet";
pub const WRITE_ACK: &str = "write_acknowledgement";
pub const ACK_PACKET: &str = "acknowledge_packet";
pub const TIMEOUT: &str = "timeout_packet";

/// The content of the `key` field for the attribute containing the connection identifier.
const CHANNEL_ID_ATTRIBUTE_KEY: &str = "channel_id";

/// The content of the `key` field for the attribute containing the port identifier.
const PORT_ID_ATTRIBUTE_KEY: &str = "port_id";

/// The content of the `type` field for the event that a chain produces upon executing a channel handshake transaction.
const OPEN_INIT_EVENT_TYPE: &str = "channel_open_init";
const OPEN_TRY_EVENT_TYPE: &str = "channel_open_try";
const OPEN_ACK_EVENT_TYPE: &str = "channel_open_ack";
const OPEN_CONFIRM_EVENT_TYPE: &str = "channel_open_confirm";
const CLOSE_INIT_EVENT_TYPE: &str = "channel_close_init";
const CLOSE_CONFIRM_EVENT_TYPE: &str = "channel_close_confirm";

/// A list of all the event `type`s that this module is capable of parsing
fn event_types() -> HashSet<String> {
    HashSet::from_iter(
        vec![
            OPEN_INIT_EVENT_TYPE.to_string(),
            OPEN_TRY_EVENT_TYPE.to_string(),
            OPEN_ACK_EVENT_TYPE.to_string(),
            OPEN_CONFIRM_EVENT_TYPE.to_string(),
            CLOSE_INIT_EVENT_TYPE.to_string(),
            CLOSE_CONFIRM_EVENT_TYPE.to_string(),
        ]
            .iter()
            .cloned(),
    )
}

pub fn try_from_tx(event: tendermint::abci::Event) -> Option<IBCEvent> {
    event_types().get(&event.type_str)?; // Quit fast if the event type is irrelevant
    let mut attr = Attributes::default();


    for tag in event.attributes {
        match tag.key.as_ref() {
            CHANNEL_ID_ATTRIBUTE_KEY => attr.channel_id = tag.value.to_string().parse().unwrap(),
            PORT_ID_ATTRIBUTE_KEY => attr.port_id = tag.value.to_string().parse().unwrap(),
            _ => {}
        }
    }

    match event.type_str.as_str() {
        OPEN_INIT_EVENT_TYPE => Some(IBCEvent::OpenInitChannel(OpenInit::from(attr))),
        OPEN_TRY_EVENT_TYPE => Some(IBCEvent::OpenTryChannel(OpenTry::from(attr))),
        OPEN_ACK_EVENT_TYPE => Some(IBCEvent::OpenAckChannel(OpenAck::from(attr))),
        OPEN_CONFIRM_EVENT_TYPE => Some(IBCEvent::OpenConfirmChannel(OpenConfirm::from(attr))),
        CLOSE_INIT_EVENT_TYPE => Some(IBCEvent::CloseInitChannel(CloseInit::from(attr))),
        CLOSE_CONFIRM_EVENT_TYPE => Some(IBCEvent::CloseConfirmChannel(CloseConfirm::from(attr))),
        _ => None,
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct Attributes {
    pub height: block::Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            height: Default::default(),
            port_id: Default::default(),
            channel_id: Default::default()
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenInit {
    pub common_attributes: Attributes,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: ChannelId,
}

impl From<Attributes> for OpenInit {
    fn from(attrs: Attributes) -> Self {
        OpenInit {
            common_attributes: attrs,
            connection_id: Default::default(),
            counterparty_port_id: Default::default(),
            counterparty_channel_id: Default::default()
        }
    }
}

impl TryFrom<RawObject> for OpenInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenInit {
            common_attributes: Attributes {
                height: obj.height,
                port_id: attribute!(obj, "channel_open_init.port_id"),
                channel_id: attribute!(obj, "channel_open_init.channel_id"),
            },
            connection_id: attribute!(obj, "channel_open_init.connection_id"),
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
    pub common_attributes: Attributes,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: ChannelId,
}

impl From<Attributes> for OpenTry {
    fn from(attrs: Attributes) -> Self {
        OpenTry {
            common_attributes: attrs,
            connection_id: Default::default(),
            counterparty_port_id: Default::default(),
            counterparty_channel_id: Default::default()
        }
    }
}

impl TryFrom<RawObject> for OpenTry {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenTry {
            common_attributes: Attributes {
                height: obj.height,
                port_id: attribute!(obj, "channel_open_try.port_id"),
                channel_id: attribute!(obj, "channel_open_try.channel_id"),
            },
            connection_id: attribute!(obj, "channel_open_try.connection_id"),
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
pub struct OpenAck(Attributes);

impl From<Attributes> for OpenAck {
    fn from(attrs: Attributes) -> Self {
        OpenAck(attrs)
    }
}


impl TryFrom<RawObject> for OpenAck {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenAck (Attributes{
            height: obj.height,
            port_id: attribute!(obj, "channel_open_ack.port_id"),
            channel_id: attribute!(obj, "channel_open_ack.channel_id"),
        }))
    }
}

impl From<OpenAck> for IBCEvent {
    fn from(v: OpenAck) -> Self {
        IBCEvent::OpenAckChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenConfirm(Attributes);

impl From<Attributes> for OpenConfirm {
    fn from(attrs: Attributes) -> Self {
        OpenConfirm(attrs)
    }
}

impl TryFrom<RawObject> for OpenConfirm {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenConfirm(Attributes{
            height: obj.height,
            port_id: attribute!(obj, "channel_open_confirm.port_id"),
            channel_id: attribute!(obj, "channel_open_confirm.channel_id"),
        }))
    }
}

impl From<OpenConfirm> for IBCEvent {
    fn from(v: OpenConfirm) -> Self {
        IBCEvent::OpenConfirmChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CloseInit(Attributes);

impl From<Attributes> for CloseInit {
    fn from(attrs: Attributes) -> Self {
        CloseInit(attrs)
    }
}

impl TryFrom<RawObject> for CloseInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CloseInit(Attributes{
            height: obj.height,
            port_id: attribute!(obj, "channel_close_init.port_id"),
            channel_id: attribute!(obj, "channel_close_init.channel_id"),
        }))
    }
}

impl From<CloseInit> for IBCEvent {
    fn from(v: CloseInit) -> Self {
        IBCEvent::CloseInitChannel(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CloseConfirm(Attributes);

impl From<Attributes> for CloseConfirm {
    fn from(attrs: Attributes) -> Self {
        CloseConfirm(attrs)
    }
}


impl TryFrom<RawObject> for CloseConfirm {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CloseConfirm(Attributes{
            height: obj.height,
            port_id: attribute!(obj, "channel_close_confirm.port_id"),
            channel_id: attribute!(obj, "channel_close_confirm.channel_id"),
        }))
    }
}

impl From<CloseConfirm> for IBCEvent {
    fn from(v: CloseConfirm) -> Self {
        IBCEvent::CloseConfirmChannel(v)
    }
}

#[macro_export]
macro_rules! p_attribute {
    ($a:ident, $b:literal) => {{
        let nb = format!("{}.{}", $a.action, $b);
        $a.events.get(&nb).ok_or(nb)?[$a.idx].parse()?
    }};
}

impl TryFrom<RawObject> for Packet {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height_str: String = p_attribute!(obj, "packet_timeout_height");
        let sequence: u64 = p_attribute!(obj, "packet_sequence");
        Ok(Packet {
            sequence: sequence.into(),
            source_port: p_attribute!(obj, "packet_src_port"),
            source_channel: p_attribute!(obj, "packet_src_channel"),
            destination_port: p_attribute!(obj, "packet_dst_port"),
            destination_channel: p_attribute!(obj, "packet_dst_channel"),
            data: vec![],
            timeout_height: height_str.try_into()?,
            timeout_timestamp: p_attribute!(obj, "packet_timeout_timestamp"),
        })
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct SendPacket {
    pub height: block::Height,
    pub packet: Packet,
}

impl TryFrom<RawObject> for SendPacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height = obj.height;
        let data_str: String = p_attribute!(obj, "packet_data");
        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());
        Ok(SendPacket { height, packet })
    }
}

impl From<SendPacket> for IBCEvent {
    fn from(v: SendPacket) -> Self {
        IBCEvent::SendPacketChannel(v)
    }
}

impl std::fmt::Display for SendPacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?} {} {}", self.height, SEND_PACKET, self.packet)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ReceivePacket {
    pub height: block::Height,
    pub packet: Packet,
}

impl TryFrom<RawObject> for ReceivePacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height = obj.height;
        let data_str: String = p_attribute!(obj, "packet_data");
        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());
        Ok(ReceivePacket { height, packet })
    }
}

impl From<ReceivePacket> for IBCEvent {
    fn from(v: ReceivePacket) -> Self {
        IBCEvent::ReceivePacketChannel(v)
    }
}

impl std::fmt::Display for ReceivePacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?} {} {}", self.height, RECV_PACKET, self.packet)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct WriteAcknowledgement {
    pub height: block::Height,
    pub packet: Packet,
    pub ack: Vec<u8>,
}

impl TryFrom<RawObject> for WriteAcknowledgement {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height = obj.height;
        let data_str: String = p_attribute!(obj, "packet_data");
        let ack_str: String = p_attribute!(obj, "packet_ack");
        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());
        Ok(WriteAcknowledgement {
            height,
            packet,
            ack: Vec::from(ack_str.as_str().as_bytes()),
        })
    }
}

impl From<WriteAcknowledgement> for IBCEvent {
    fn from(v: WriteAcknowledgement) -> Self {
        IBCEvent::WriteAcknowledgementChannel(v)
    }
}

impl std::fmt::Display for WriteAcknowledgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?} {} {}", self.height, WRITE_ACK, self.packet)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct AcknowledgePacket {
    pub height: block::Height,
    pub packet: Packet,
}

impl TryFrom<RawObject> for AcknowledgePacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height = obj.height;
        let packet = Packet::try_from(obj)?;
        Ok(AcknowledgePacket { height, packet })
    }
}

impl From<AcknowledgePacket> for IBCEvent {
    fn from(v: AcknowledgePacket) -> Self {
        IBCEvent::AcknowledgePacketChannel(v)
    }
}

impl std::fmt::Display for AcknowledgePacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{} {} {}", self.height, ACK_PACKET, self.packet)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct TimeoutPacket {
    pub height: block::Height,
    pub packet: Packet,
}

impl TryFrom<RawObject> for TimeoutPacket {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(TimeoutPacket {
            height: obj.height,
            packet: Packet::try_from(obj)?,
        })
    }
}

impl From<TimeoutPacket> for IBCEvent {
    fn from(v: TimeoutPacket) -> Self {
        IBCEvent::TimeoutPacketChannel(v)
    }
}

impl std::fmt::Display for TimeoutPacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{} {} {}", self.height, TIMEOUT, self.packet)
    }
}
