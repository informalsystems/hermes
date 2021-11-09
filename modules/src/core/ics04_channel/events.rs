//! Types for the IBC events emitted from Tendermint Websocket by the channels module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::height::Height;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::events::{extract_attribute, Error as EventError, IbcEvent, IbcEventType, RawObject};
use crate::prelude::*;

/// Channel event attribute keys
const HEIGHT_ATTRIBUTE_KEY: &str = "height";
const CONNECTION_ID_ATTRIBUTE_KEY: &str = "connection_id";
const CHANNEL_ID_ATTRIBUTE_KEY: &str = "channel_id";
const PORT_ID_ATTRIBUTE_KEY: &str = "port_id";
const COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY: &str = "counterparty_channel_id";
const COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY: &str = "counterparty_port_id";

/// Packet event attribute keys
const PKT_SEQ_ATTRIBUTE_KEY: &str = "packet_sequence";
const PKT_DATA_ATTRIBUTE_KEY: &str = "packet_data";
const PKT_SRC_PORT_ATTRIBUTE_KEY: &str = "packet_src_port";
const PKT_SRC_CHANNEL_ATTRIBUTE_KEY: &str = "packet_src_channel";
const PKT_DST_PORT_ATTRIBUTE_KEY: &str = "packet_dst_port";
const PKT_DST_CHANNEL_ATTRIBUTE_KEY: &str = "packet_dst_channel";
const PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY: &str = "packet_timeout_height";
const PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY: &str = "packet_timeout_timestamp";

const PKT_ACK_ATTRIBUTE_KEY: &str = "packet_ack";

pub fn try_from_tx(event: &tendermint::abci::Event) -> Option<IbcEvent> {
    match event.type_str.parse() {
        Ok(IbcEventType::OpenInitChannel) => extract_attributes_from_tx(event)
            .map(OpenInit::from)
            .map(IbcEvent::OpenInitChannel)
            .ok(),
        Ok(IbcEventType::OpenTryChannel) => extract_attributes_from_tx(event)
            .map(OpenTry::from)
            .map(IbcEvent::OpenTryChannel)
            .ok(),
        Ok(IbcEventType::OpenAckChannel) => extract_attributes_from_tx(event)
            .map(OpenAck::from)
            .map(IbcEvent::OpenAckChannel)
            .ok(),
        Ok(IbcEventType::OpenConfirmChannel) => extract_attributes_from_tx(event)
            .map(OpenConfirm::from)
            .map(IbcEvent::OpenConfirmChannel)
            .ok(),
        Ok(IbcEventType::CloseInitChannel) => extract_attributes_from_tx(event)
            .map(CloseInit::from)
            .map(IbcEvent::CloseInitChannel)
            .ok(),
        Ok(IbcEventType::CloseConfirmChannel) => extract_attributes_from_tx(event)
            .map(CloseConfirm::from)
            .map(IbcEvent::CloseConfirmChannel)
            .ok(),
        Ok(IbcEventType::SendPacket) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::SendPacket(SendPacket {
                        height: Default::default(),
                        packet,
                    })
                })
                .ok()
        }
        Ok(IbcEventType::WriteAck) => extract_packet_and_write_ack_from_tx(event)
            .map(|(packet, write_ack)| {
                IbcEvent::WriteAcknowledgement(WriteAcknowledgement {
                    height: Default::default(),
                    packet,
                    ack: write_ack,
                })
            })
            .ok(),
        Ok(IbcEventType::AckPacket) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::AcknowledgePacket(AcknowledgePacket {
                        height: Default::default(),
                        packet,
                    })
                })
                .ok()
        }
        Ok(IbcEventType::Timeout) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::TimeoutPacket(TimeoutPacket {
                        height: Default::default(),
                        packet,
                    })
                })
                .ok()
        }
        _ => None,
    }
}

fn extract_attributes_from_tx(event: &tendermint::abci::Event) -> Result<Attributes, Error> {
    let mut attr = Attributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            PORT_ID_ATTRIBUTE_KEY => attr.port_id = value.parse().map_err(Error::identifier)?,
            CHANNEL_ID_ATTRIBUTE_KEY => {
                attr.channel_id = value.parse().ok();
            }
            CONNECTION_ID_ATTRIBUTE_KEY => {
                attr.connection_id = value.parse().map_err(Error::identifier)?;
            }
            COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_port_id = value.parse().map_err(Error::identifier)?;
            }
            COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY => {
                attr.counterparty_channel_id = value.parse().ok();
            }
            _ => {}
        }
    }

    Ok(attr)
}

fn extract_packet_and_write_ack_from_tx(
    event: &tendermint::abci::Event,
) -> Result<(Packet, Vec<u8>), Error> {
    let mut packet = Packet::default();
    let mut write_ack: Vec<u8> = Vec::new();
    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            PKT_SRC_PORT_ATTRIBUTE_KEY => {
                packet.source_port = value.parse().map_err(Error::identifier)?;
            }
            PKT_SRC_CHANNEL_ATTRIBUTE_KEY => {
                packet.source_channel = value.parse().map_err(Error::identifier)?;
            }
            PKT_DST_PORT_ATTRIBUTE_KEY => {
                packet.destination_port = value.parse().map_err(Error::identifier)?;
            }
            PKT_DST_CHANNEL_ATTRIBUTE_KEY => {
                packet.destination_channel = value.parse().map_err(Error::identifier)?;
            }
            PKT_SEQ_ATTRIBUTE_KEY => {
                packet.sequence = value
                    .parse::<u64>()
                    .map_err(|e| Error::invalid_string_as_sequence(value.to_string(), e))?
                    .into()
            }
            PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY => {
                packet.timeout_height =
                    value.parse().map_err(|_| Error::invalid_timeout_height())?;
            }
            PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY => {
                packet.timeout_timestamp = value.parse().unwrap();
            }
            PKT_DATA_ATTRIBUTE_KEY => {
                packet.data = Vec::from(value.as_bytes());
            }
            PKT_ACK_ATTRIBUTE_KEY => {
                write_ack = Vec::from(value.as_bytes());
            }
            _ => {}
        }
    }

    Ok((packet, write_ack))
}

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
        Attributes {
            height: Default::default(),
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
                value: channel_id.as_str().parse().unwrap(),
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
                value: channel_id.as_str().parse().unwrap(),
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
            value: p.timeout_height.to_string().parse().unwrap(),
        };
        attributes.push(timeout_height);
        let timeout_timestamp = Tag {
            key: PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY.parse().unwrap(),
            value: p
                .timeout_timestamp
                .as_nanoseconds()
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenInit(pub Attributes);

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

impl From<Attributes> for OpenInit {
    fn from(attrs: Attributes) -> Self {
        OpenInit(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenTry(pub Attributes);

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

impl From<Attributes> for OpenTry {
    fn from(attrs: Attributes) -> Self {
        OpenTry(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenAck(pub Attributes);

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

impl From<Attributes> for OpenAck {
    fn from(attrs: Attributes) -> Self {
        OpenAck(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenConfirm(pub Attributes);

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

impl From<Attributes> for OpenConfirm {
    fn from(attrs: Attributes) -> Self {
        OpenConfirm(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct CloseInit(pub Attributes);

impl CloseInit {
    pub fn port_id(&self) -> &PortId {
        &self.0.port_id
    }

    pub fn channel_id(&self) -> &ChannelId {
        // FIXME(romac): Rework encoding of IbcEvents which use `Attributes`
        self.0
            .channel_id
            .as_ref()
            .expect("CloseInit should always have a channel_id")
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

impl From<Attributes> for CloseInit {
    fn from(attrs: Attributes) -> Self {
        CloseInit(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct CloseConfirm(pub Attributes);

impl CloseConfirm {
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

impl From<Attributes> for CloseConfirm {
    fn from(attrs: Attributes) -> Self {
        CloseConfirm(attrs)
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

impl TryFrom<RawObject> for SendPacket {
    type Error = EventError;

    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let height = obj.height;
        let data_str: String = extract_attribute(&obj, &format!("{}.packet_data", obj.action))?;

        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());

        Ok(SendPacket { height, packet })
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

impl core::fmt::Display for ReceivePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "ReceivePacket - h:{}, {}", self.height, self.packet)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

impl core::fmt::Display for TimeoutOnClosePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "TimeoutOnClosePacket - h:{}, {}",
            self.height, self.packet
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::ics04_channel::packet::Sequence;
    use crate::timestamp::Timestamp;

    #[test]
    fn channel_event_to_abci_event() {
        let attributes = Attributes {
            height: Height::default(),
            port_id: "test_port".parse().unwrap(),
            channel_id: Some("test_channel".parse().unwrap()),
            connection_id: "test_connection".parse().unwrap(),
            counterparty_port_id: "counterparty_test_port".parse().unwrap(),
            counterparty_channel_id: Some("counterparty_test_channel".parse().unwrap()),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = OpenTry::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = OpenAck::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = OpenConfirm::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_confirm.clone()));
        let close_init = CloseInit::from(attributes.clone());
        abci_events.push(AbciEvent::from(close_init.clone()));
        let close_confirm = CloseConfirm::from(attributes);
        abci_events.push(AbciEvent::from(close_confirm.clone()));

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::OpenInitChannel(e) => assert_eq!(e.0, open_init.0),
                    IbcEvent::OpenTryChannel(e) => assert_eq!(e.0, open_try.0),
                    IbcEvent::OpenAckChannel(e) => assert_eq!(e.0, open_ack.0),
                    IbcEvent::OpenConfirmChannel(e) => assert_eq!(e.0, open_confirm.0),
                    IbcEvent::CloseInitChannel(e) => assert_eq!(e.0, close_init.0),
                    IbcEvent::CloseConfirmChannel(e) => assert_eq!(e.0, close_confirm.0),
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }

    #[test]
    fn packet_event_to_abci_event() {
        let packet = Packet {
            sequence: Sequence::from(10),
            source_port: "a_test_port".parse().unwrap(),
            source_channel: "a_test_channel".parse().unwrap(),
            destination_port: "b_test_port".parse().unwrap(),
            destination_channel: "b_test_channel".parse().unwrap(),
            data: "test_data".as_bytes().to_vec(),
            timeout_height: Height::new(1, 10),
            timeout_timestamp: Timestamp::from_datetime(chrono::offset::Utc::now()),
        };
        let mut abci_events = vec![];
        let send_packet = SendPacket {
            height: Height::default(),
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(send_packet.clone()).unwrap());
        let write_ack = WriteAcknowledgement {
            height: Height::default(),
            packet: packet.clone(),
            ack: "test_ack".as_bytes().to_vec(),
        };
        abci_events.push(AbciEvent::try_from(write_ack.clone()).unwrap());
        let ack_packet = AcknowledgePacket {
            height: Height::default(),
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(ack_packet.clone()).unwrap());
        let timeout_packet = TimeoutPacket {
            height: Height::default(),
            packet,
        };
        abci_events.push(AbciEvent::try_from(timeout_packet.clone()).unwrap());

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::SendPacket(e) => assert_eq!(e.packet, send_packet.packet),
                    IbcEvent::WriteAcknowledgement(e) => {
                        assert_eq!(e.packet, write_ack.packet);
                        assert_eq!(e.ack, write_ack.ack);
                    }
                    IbcEvent::AcknowledgePacket(e) => assert_eq!(e.packet, ack_packet.packet),
                    IbcEvent::TimeoutPacket(e) => assert_eq!(e.packet, timeout_packet.packet),
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
