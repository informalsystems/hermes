//! Types for the IBC events emitted from Tendermint Websocket by the channels module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::height::Height;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::events::{Error as EventError, IbcEvent, IbcEventType};
use crate::prelude::*;

/// Channel event attribute keys
pub const HEIGHT_ATTRIBUTE_KEY: &str = "height";
pub const CONNECTION_ID_ATTRIBUTE_KEY: &str = "connection_id";
pub const CHANNEL_ID_ATTRIBUTE_KEY: &str = "channel_id";
pub const PORT_ID_ATTRIBUTE_KEY: &str = "port_id";
pub const COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY: &str = "counterparty_channel_id";
pub const COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY: &str = "counterparty_port_id";

/// Packet event attribute keys
pub const PKT_SEQ_ATTRIBUTE_KEY: &str = "packet_sequence";
pub const PKT_DATA_ATTRIBUTE_KEY: &str = "packet_data";
pub const PKT_SRC_PORT_ATTRIBUTE_KEY: &str = "packet_src_port";
pub const PKT_SRC_CHANNEL_ATTRIBUTE_KEY: &str = "packet_src_channel";
pub const PKT_DST_PORT_ATTRIBUTE_KEY: &str = "packet_dst_port";
pub const PKT_DST_CHANNEL_ATTRIBUTE_KEY: &str = "packet_dst_channel";
pub const PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY: &str = "packet_timeout_height";
pub const PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY: &str = "packet_timeout_timestamp";
pub const PKT_ACK_ATTRIBUTE_KEY: &str = "packet_ack";

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attributes {
    pub height: Height,
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Attributes {
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
}

impl Default for Attributes {
    fn default() -> Self {
        Self {
            height: Height::new(0, 1).unwrap(),
            port_id: Default::default(),
            channel_id: Default::default(),
            connection_id: Default::default(),
            counterparty_port_id: Default::default(),
            counterparty_channel_id: Default::default(),
        }
    }
}

/// Convert attributes to Tendermint ABCI tags
///
/// # Note
/// The parsing of `Key`s and `Value`s never fails, because the
/// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
/// is infallible, even if it is not represented in the error type.
/// Once tendermint-rs improves the API of the `Key` and `Value` types,
/// we will be able to remove the `.parse().unwrap()` calls.
impl From<Attributes> for Vec<Tag> {
    fn from(a: Attributes) -> Self {
        let mut attributes = vec![];
        let height = Tag {
            key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        attributes.push(height);
        let port_id = Tag {
            key: PORT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.port_id.to_string().parse().unwrap(),
        };
        attributes.push(port_id);
        if let Some(channel_id) = a.channel_id {
            let channel_id = Tag {
                key: CHANNEL_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: channel_id.to_string().parse().unwrap(),
            };
            attributes.push(channel_id);
        }
        let connection_id = Tag {
            key: CONNECTION_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.connection_id.to_string().parse().unwrap(),
        };
        attributes.push(connection_id);
        let counterparty_port_id = Tag {
            key: COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.counterparty_port_id.to_string().parse().unwrap(),
        };
        attributes.push(counterparty_port_id);
        if let Some(channel_id) = a.counterparty_channel_id {
            let channel_id = Tag {
                key: COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: channel_id.to_string().parse().unwrap(),
            };
            attributes.push(channel_id);
        }
        attributes
    }
}

/// Convert attributes to Tendermint ABCI tags
///
/// # Note
/// The parsing of `Key`s and `Value`s never fails, because the
/// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
/// is infallible, even if it is not represented in the error type.
/// Once tendermint-rs improves the API of the `Key` and `Value` types,
/// we will be able to remove the `.parse().unwrap()` calls.
impl TryFrom<Packet> for Vec<Tag> {
    type Error = Error;
    fn try_from(p: Packet) -> Result<Self, Self::Error> {
        let mut attributes = vec![];
        let src_port = Tag {
            key: PKT_SRC_PORT_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.source_port.to_string().parse().unwrap(),
        };
        attributes.push(src_port);
        let src_channel = Tag {
            key: PKT_SRC_CHANNEL_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.source_channel.to_string().parse().unwrap(),
        };
        attributes.push(src_channel);
        let dst_port = Tag {
            key: PKT_DST_PORT_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.destination_port.to_string().parse().unwrap(),
        };
        attributes.push(dst_port);
        let dst_channel = Tag {
            key: PKT_DST_CHANNEL_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.destination_channel.to_string().parse().unwrap(),
        };
        attributes.push(dst_channel);
        let sequence = Tag {
            key: PKT_SEQ_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.sequence.to_string().parse().unwrap(),
        };
        attributes.push(sequence);
        let timeout_height = Tag {
            key: PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: p.timeout_height.into(),
        };
        attributes.push(timeout_height);
        let timeout_timestamp = Tag {
            key: PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY.parse().unwrap(),
            value: p
                .timeout_timestamp
                .nanoseconds()
                .to_string()
                .parse()
                .unwrap(),
        };
        attributes.push(timeout_timestamp);
        let val =
            String::from_utf8(p.data).expect("hex-encoded string should always be valid UTF-8");
        let packet_data = Tag {
            key: PKT_DATA_ATTRIBUTE_KEY.parse().unwrap(),
            value: val.parse().unwrap(),
        };
        attributes.push(packet_data);
        let ack = Tag {
            key: PKT_ACK_ATTRIBUTE_KEY.parse().unwrap(),
            value: "".parse().unwrap(),
        };
        attributes.push(ack);
        Ok(attributes)
    }
}

pub trait EventType {
    fn event_type() -> IbcEventType;
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenInit(Attributes);

impl OpenInit {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.0.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<Attributes> for OpenInit {
    type Error = EventError;

    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        Ok(OpenInit(attrs))
    }
}

impl From<OpenInit> for IbcEvent {
    fn from(v: OpenInit) -> Self {
        IbcEvent::OpenInitChannel(v)
    }
}

impl From<OpenInit> for AbciEvent {
    fn from(v: OpenInit) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenInitChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl EventType for OpenInit {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenInitChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenTry(Attributes);

impl OpenTry {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.0.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<Attributes> for OpenTry {
    type Error = EventError;

    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        Ok(OpenTry(attrs))
    }
}

impl From<OpenTry> for IbcEvent {
    fn from(v: OpenTry) -> Self {
        IbcEvent::OpenTryChannel(v)
    }
}

impl From<OpenTry> for AbciEvent {
    fn from(v: OpenTry) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenTryChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl EventType for OpenTry {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenTryChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenAck(Attributes);

impl OpenAck {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.0.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.0.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<Attributes> for OpenAck {
    type Error = EventError;

    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        Ok(OpenAck(attrs))
    }
}

impl From<OpenAck> for IbcEvent {
    fn from(v: OpenAck) -> Self {
        IbcEvent::OpenAckChannel(v)
    }
}

impl From<OpenAck> for AbciEvent {
    fn from(v: OpenAck) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenAckChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl EventType for OpenAck {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenAckChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenConfirm(Attributes);

impl OpenConfirm {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.0.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<Attributes> for OpenConfirm {
    type Error = EventError;

    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        Ok(OpenConfirm(attrs))
    }
}

impl From<OpenConfirm> for IbcEvent {
    fn from(v: OpenConfirm) -> Self {
        IbcEvent::OpenConfirmChannel(v)
    }
}

impl From<OpenConfirm> for AbciEvent {
    fn from(v: OpenConfirm) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenConfirmChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl EventType for OpenConfirm {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenConfirmChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CloseInit(Attributes);

impl CloseInit {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }

    pub fn channel_id(&self) -> ChannelId {
        // Safety - We ensure that the `channel_id` is present in `TryFrom<Attributes>`
        self.0.channel_id.clone().unwrap()
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.0.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.0.counterparty_channel_id.as_ref()
    }

    pub fn height(&self) -> Height {
        self.0.height
    }

    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<Attributes> for CloseInit {
    type Error = EventError;
    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        if let Some(_channel_id) = attrs.channel_id() {
            Ok(CloseInit(attrs))
        } else {
            Err(EventError::channel(Error::missing_channel_id()))
        }
    }
}

impl From<CloseInit> for IbcEvent {
    fn from(v: CloseInit) -> Self {
        IbcEvent::CloseInitChannel(v)
    }
}

impl From<CloseInit> for AbciEvent {
    fn from(v: CloseInit) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::CloseInitChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl core::fmt::Display for CloseInit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "{} {} {:?}",
            self.height(),
            IbcEventType::CloseInitChannel.as_str(),
            self.0
        )
    }
}

impl EventType for CloseInit {
    fn event_type() -> IbcEventType {
        IbcEventType::CloseInitChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CloseConfirm(Attributes);

impl CloseConfirm {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.0.channel_id.as_ref()
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<Attributes> for CloseConfirm {
    type Error = EventError;

    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        Ok(CloseConfirm(attrs))
    }
}

impl From<CloseConfirm> for IbcEvent {
    fn from(v: CloseConfirm) -> Self {
        IbcEvent::CloseConfirmChannel(v)
    }
}

impl From<CloseConfirm> for AbciEvent {
    fn from(v: CloseConfirm) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::CloseConfirmChannel.as_str().to_string(),
            attributes,
        }
    }
}

impl EventType for CloseConfirm {
    fn event_type() -> IbcEventType {
        IbcEventType::CloseConfirmChannel
    }
}

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct SendPacket {
    pub height: Height,
    pub packet: Packet,
}

impl SendPacket {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
    pub fn dst_port_id(&self) -> &PortId {
        &self.packet.destination_port
    }
    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.packet.destination_channel
    }
}

impl From<SendPacket> for IbcEvent {
    fn from(v: SendPacket) -> Self {
        IbcEvent::SendPacket(v)
    }
}

impl TryFrom<SendPacket> for AbciEvent {
    type Error = Error;

    fn try_from(v: SendPacket) -> Result<Self, Self::Error> {
        let attributes = Vec::<Tag>::try_from(v.packet)?;
        Ok(AbciEvent {
            type_str: IbcEventType::SendPacket.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for SendPacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "SendPacket - h:{}, {}", self.height, self.packet)
    }
}

impl core::fmt::Debug for SendPacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "SendPacket - h:{}, {}", self.height, self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct ReceivePacket {
    pub height: Height,
    pub packet: Packet,
}

impl ReceivePacket {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
    pub fn dst_port_id(&self) -> &PortId {
        &self.packet.destination_port
    }
    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.packet.destination_channel
    }
}

impl From<ReceivePacket> for IbcEvent {
    fn from(v: ReceivePacket) -> Self {
        IbcEvent::ReceivePacket(v)
    }
}

impl TryFrom<ReceivePacket> for AbciEvent {
    type Error = Error;

    fn try_from(v: ReceivePacket) -> Result<Self, Self::Error> {
        let attributes = Vec::<Tag>::try_from(v.packet)?;
        Ok(AbciEvent {
            type_str: IbcEventType::ReceivePacket.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for ReceivePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "ReceivePacket - h:{}, {}", self.height, self.packet)
    }
}

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct WriteAcknowledgement {
    pub height: Height,
    pub packet: Packet,
    #[serde(serialize_with = "crate::serializers::ser_hex_upper")]
    pub ack: Vec<u8>,
}

impl WriteAcknowledgement {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
    pub fn dst_port_id(&self) -> &PortId {
        &self.packet.destination_port
    }
    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.packet.destination_channel
    }
}

impl From<WriteAcknowledgement> for IbcEvent {
    fn from(v: WriteAcknowledgement) -> Self {
        IbcEvent::WriteAcknowledgement(v)
    }
}

impl TryFrom<WriteAcknowledgement> for AbciEvent {
    type Error = Error;

    fn try_from(v: WriteAcknowledgement) -> Result<Self, Self::Error> {
        let mut attributes = Vec::<Tag>::try_from(v.packet)?;
        let val =
            String::from_utf8(v.ack).expect("hex-encoded string should always be valid UTF-8");
        // No actual conversion from string to `Tag::Key` or `Tag::Value`
        let ack = Tag {
            key: PKT_ACK_ATTRIBUTE_KEY.parse().unwrap(),
            value: val.parse().unwrap(),
        };
        attributes.push(ack);
        Ok(AbciEvent {
            type_str: IbcEventType::WriteAck.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for WriteAcknowledgement {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "WriteAcknowledgement - h:{}, {}",
            self.height, self.packet
        )
    }
}

impl core::fmt::Debug for WriteAcknowledgement {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "WriteAcknowledgement - h:{}, {}",
            self.height, self.packet
        )
    }
}

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct AcknowledgePacket {
    pub height: Height,
    pub packet: Packet,
}

impl AcknowledgePacket {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
}

impl From<AcknowledgePacket> for IbcEvent {
    fn from(v: AcknowledgePacket) -> Self {
        IbcEvent::AcknowledgePacket(v)
    }
}

impl TryFrom<AcknowledgePacket> for AbciEvent {
    type Error = Error;

    fn try_from(v: AcknowledgePacket) -> Result<Self, Self::Error> {
        let attributes = Vec::<Tag>::try_from(v.packet)?;
        Ok(AbciEvent {
            type_str: IbcEventType::AckPacket.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for AcknowledgePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "h:{}, {}", self.height, self.packet)
    }
}

impl core::fmt::Debug for AcknowledgePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "AcknowledgePacket - h:{}, {}", self.height, self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimeoutPacket {
    pub height: Height,
    pub packet: Packet,
}

impl TimeoutPacket {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
    pub fn dst_port_id(&self) -> &PortId {
        &self.packet.destination_port
    }
    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.packet.destination_channel
    }
}

impl From<TimeoutPacket> for IbcEvent {
    fn from(v: TimeoutPacket) -> Self {
        IbcEvent::TimeoutPacket(v)
    }
}

impl TryFrom<TimeoutPacket> for AbciEvent {
    type Error = Error;

    fn try_from(v: TimeoutPacket) -> Result<Self, Self::Error> {
        let attributes = Vec::<Tag>::try_from(v.packet)?;
        Ok(AbciEvent {
            type_str: IbcEventType::Timeout.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for TimeoutPacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "TimeoutPacket - h:{}, {}", self.height, self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimeoutOnClosePacket {
    pub height: Height,
    pub packet: Packet,
}

impl TimeoutOnClosePacket {
    pub fn height(&self) -> Height {
        self.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
    pub fn dst_port_id(&self) -> &PortId {
        &self.packet.destination_port
    }
    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.packet.destination_channel
    }
}

impl From<TimeoutOnClosePacket> for IbcEvent {
    fn from(v: TimeoutOnClosePacket) -> Self {
        IbcEvent::TimeoutOnClosePacket(v)
    }
}

impl TryFrom<TimeoutOnClosePacket> for AbciEvent {
    type Error = Error;

    fn try_from(v: TimeoutOnClosePacket) -> Result<Self, Self::Error> {
        let attributes = Vec::<Tag>::try_from(v.packet)?;
        Ok(AbciEvent {
            type_str: IbcEventType::TimeoutOnClose.as_str().to_string(),
            attributes,
        })
    }
}

impl core::fmt::Display for TimeoutOnClosePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "TimeoutOnClosePacket - h:{}, {}",
            self.height, self.packet
        )
    }
}
