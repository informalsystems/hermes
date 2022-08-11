//! Types for the IBC events emitted from Tendermint Websocket by the channels module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::height::{Height, HeightErrorDetail};
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::events::{Error as EventError, IbcEvent, IbcEventType};
use crate::prelude::*;

use super::timeout::TimeoutHeight;

/// Channel event attribute keys
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

#[derive(Debug, Default, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attributes {
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
pub struct OpenInit {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl OpenInit {
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }
}

impl From<OpenInit> for Attributes {
    fn from(ev: OpenInit) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}

impl TryFrom<&AbciEvent> for OpenInit {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => OpenInit::try_from(attrs).map_err(|_| Error::implementation_specific()),
            Err(e) => Err(e),
        }
    }
}

impl From<OpenInit> for IbcEvent {
    fn from(v: OpenInit) -> Self {
        IbcEvent::OpenInitChannel(v)
    }
}

impl EventType for OpenInit {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenInitChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenTry {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl From<OpenTry> for Attributes {
    fn from(ev: OpenTry) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}
impl OpenTry {
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }
}

impl TryFrom<&AbciEvent> for OpenTry {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => OpenTry::try_from(attrs).map_err(|_| Error::implementation_specific()),
            Err(e) => Err(e),
        }
    }
}

impl From<OpenTry> for IbcEvent {
    fn from(v: OpenTry) -> Self {
        IbcEvent::OpenTryChannel(v)
    }
}

impl EventType for OpenTry {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenTryChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenAck {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub counterparty_channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
}

impl From<OpenAck> for Attributes {
    fn from(ev: OpenAck) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}

impl OpenAck {
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<&AbciEvent> for OpenAck {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => OpenAck::try_from(attrs).map_err(|_| Error::implementation_specific()),
            Err(e) => Err(e),
        }
    }
}

impl From<OpenAck> for IbcEvent {
    fn from(v: OpenAck) -> Self {
        IbcEvent::OpenAckChannel(v)
    }
}

impl EventType for OpenAck {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenAckChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct OpenConfirm {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl From<OpenConfirm> for Attributes {
    fn from(ev: OpenConfirm) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}

impl TryFrom<&AbciEvent> for OpenConfirm {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => OpenConfirm::try_from(attrs).map_err(|_| Error::implementation_specific()),
            Err(e) => Err(e),
        }
    }
}

impl OpenConfirm {
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }
}

impl From<OpenConfirm> for IbcEvent {
    fn from(v: OpenConfirm) -> Self {
        IbcEvent::OpenConfirmChannel(v)
    }
}

impl EventType for OpenConfirm {
    fn event_type() -> IbcEventType {
        IbcEventType::OpenConfirmChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CloseInit {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl From<CloseInit> for Attributes {
    fn from(ev: CloseInit) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: Some(ev.channel_id),
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}

impl CloseInit {
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<Attributes> for CloseInit {
    type Error = EventError;
    fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
        if let Some(channel_id) = attrs.channel_id() {
            Ok(CloseInit {
                port_id: attrs.port_id.clone(),
                channel_id: channel_id.clone(),
                connection_id: attrs.connection_id.clone(),
                counterparty_port_id: attrs.counterparty_port_id.clone(),
                counterparty_channel_id: attrs.counterparty_channel_id,
            })
        } else {
            Err(EventError::channel(Error::missing_channel_id()))
        }
    }
}

impl TryFrom<&AbciEvent> for CloseInit {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => CloseInit::try_from(attrs).map_err(|_| Error::implementation_specific()),
            Err(e) => Err(e),
        }
    }
}

impl From<CloseInit> for IbcEvent {
    fn from(v: CloseInit) -> Self {
        IbcEvent::CloseInitChannel(v)
    }
}

impl core::fmt::Display for CloseInit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "{} {:?}",
            IbcEventType::CloseInitChannel.as_str(),
            Attributes::from(self.clone())
        )
    }
}

impl EventType for CloseInit {
    fn event_type() -> IbcEventType {
        IbcEventType::CloseInitChannel
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CloseConfirm {
    pub channel_id: Option<ChannelId>,
    pub port_id: PortId,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl From<CloseConfirm> for Attributes {
    fn from(ev: CloseConfirm) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            connection_id: ev.connection_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
        }
    }
}

impl TryFrom<&AbciEvent> for CloseConfirm {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        match extract_attributes_from_tx(abci_event) {
            Ok(attrs) => {
                CloseConfirm::try_from(attrs).map_err(|_| Error::implementation_specific())
            }
            Err(e) => Err(e),
        }
    }
}

impl CloseConfirm {
    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }
}

impl From<CloseConfirm> for IbcEvent {
    fn from(v: CloseConfirm) -> Self {
        IbcEvent::CloseConfirmChannel(v)
    }
}

impl EventType for CloseConfirm {
    fn event_type() -> IbcEventType {
        IbcEventType::CloseConfirmChannel
    }
}

macro_rules! impl_try_from_attribute_for_event {
    ($($event:ty),+) => {
        $(impl TryFrom<Attributes> for $event {
            type Error = EventError;

            fn try_from(attrs: Attributes) -> Result<Self, Self::Error> {
                Ok(Self {
                    port_id: attrs.port_id,
                    channel_id: attrs.channel_id,
                    connection_id: attrs.connection_id,
                    counterparty_port_id: attrs.counterparty_port_id,
                    counterparty_channel_id: attrs.counterparty_channel_id,
                })
            }
        })+
    };
}

impl_try_from_attribute_for_event!(OpenInit, OpenTry, OpenAck, OpenConfirm, CloseConfirm);

macro_rules! impl_from_ibc_to_abci_event {
    ($($event:ty),+) => {
        $(impl From<$event> for AbciEvent {
            fn from(v: $event) -> Self {
                let attributes = Vec::<Tag>::from(Attributes::from(v));
                let type_str = <$event>::event_type().as_str().to_string();
                AbciEvent {
                    type_str,
                    attributes,
                }
            }
        })+
    };
}

impl_from_ibc_to_abci_event!(
    OpenInit,
    OpenTry,
    OpenAck,
    OpenConfirm,
    CloseInit,
    CloseConfirm
);

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct SendPacket {
    pub packet: Packet,
}

impl SendPacket {
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

impl TryFrom<&AbciEvent> for SendPacket {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_packet_and_write_ack_from_tx(abci_event)
            .map(|(packet, write_ack)| {
                // This event should not have a write ack.
                debug_assert_eq!(write_ack.len(), 0);
                SendPacket { packet }
            })
            .map_err(|_| Error::abci_conversion_failed(abci_event.type_str.to_owned()))
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
        write!(f, "SendPacket - {}", self.packet)
    }
}

impl core::fmt::Debug for SendPacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "SendPacket - {}", self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct ReceivePacket {
    pub packet: Packet,
}

impl ReceivePacket {
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
        write!(f, "ReceivePacket - {}", self.packet)
    }
}

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct WriteAcknowledgement {
    pub packet: Packet,
    #[serde(serialize_with = "crate::serializers::ser_hex_upper")]
    pub ack: Vec<u8>,
}

impl WriteAcknowledgement {
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

impl TryFrom<&AbciEvent> for WriteAcknowledgement {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_packet_and_write_ack_from_tx(abci_event)
            .map(|(packet, write_ack)| WriteAcknowledgement {
                packet,
                ack: write_ack,
            })
            .map_err(|_| Error::abci_conversion_failed(abci_event.type_str.to_owned()))
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
        write!(f, "WriteAcknowledgement - {}", self.packet)
    }
}

impl core::fmt::Debug for WriteAcknowledgement {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "WriteAcknowledgement - {}", self.packet)
    }
}

#[derive(Serialize, Clone, PartialEq, Eq)]
pub struct AcknowledgePacket {
    pub packet: Packet,
}

impl AcknowledgePacket {
    pub fn src_port_id(&self) -> &PortId {
        &self.packet.source_port
    }
    pub fn src_channel_id(&self) -> &ChannelId {
        &self.packet.source_channel
    }
}

impl TryFrom<&AbciEvent> for AcknowledgePacket {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_packet_and_write_ack_from_tx(abci_event)
            .map(|(packet, write_ack)| {
                // This event should not have a write ack.
                debug_assert_eq!(write_ack.len(), 0);
                AcknowledgePacket { packet }
            })
            .map_err(|_| Error::abci_conversion_failed(abci_event.type_str.to_owned()))
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
        write!(f, "{}", self.packet)
    }
}

impl core::fmt::Debug for AcknowledgePacket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "AcknowledgePacket - {}", self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimeoutPacket {
    pub packet: Packet,
}

impl TimeoutPacket {
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

impl TryFrom<&AbciEvent> for TimeoutPacket {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_packet_and_write_ack_from_tx(abci_event)
            .map(|(packet, write_ack)| {
                // This event should not have a write ack.
                debug_assert_eq!(write_ack.len(), 0);
                TimeoutPacket { packet }
            })
            .map_err(|_| Error::abci_conversion_failed(abci_event.type_str.to_owned()))
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
        write!(f, "TimeoutPacket - {}", self.packet)
    }
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimeoutOnClosePacket {
    pub packet: Packet,
}

impl TimeoutOnClosePacket {
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
        write!(f, "TimeoutOnClosePacket - {}", self.packet)
    }
}

fn extract_attributes_from_tx(event: &AbciEvent) -> Result<Attributes, Error> {
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

fn extract_packet_and_write_ack_from_tx(event: &AbciEvent) -> Result<(Packet, Vec<u8>), Error> {
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
                packet.timeout_height = parse_timeout_height(value)?;
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

/// Parse a string into a timeout height expected to be stored in
/// `Packet.timeout_height`. We need to parse the timeout height differently
/// because of a quirk introduced in ibc-go. See comment in
/// `TryFrom<RawPacket> for Packet`.
pub fn parse_timeout_height(s: &str) -> Result<TimeoutHeight, Error> {
    match s.parse::<Height>() {
        Ok(height) => Ok(TimeoutHeight::from(height)),
        Err(e) => match e.into_detail() {
            HeightErrorDetail::ZeroHeight(_) => Ok(TimeoutHeight::no_timeout()),
            _ => Err(Error::invalid_timeout_height()),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::{core::ics04_channel::packet::Sequence, timestamp::Timestamp};

    use super::*;

    #[test]
    fn channel_event_to_abci_event() {
        let attributes = Attributes {
            port_id: "test_port".parse().unwrap(),
            channel_id: Some("channel-0".parse().unwrap()),
            connection_id: "test_connection".parse().unwrap(),
            counterparty_port_id: "counterparty_test_port".parse().unwrap(),
            counterparty_channel_id: Some("channel-1".parse().unwrap()),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = OpenTry::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = OpenAck::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = OpenConfirm::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_confirm.clone()));
        let close_init = CloseInit::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(close_init.clone()));
        let close_confirm = CloseConfirm::try_from(attributes).unwrap();
        abci_events.push(AbciEvent::from(close_confirm.clone()));

        for abci_event in abci_events {
            match IbcEvent::try_from(&abci_event).ok() {
                Some(ibc_event) => match ibc_event {
                    IbcEvent::OpenInitChannel(e) => {
                        assert_eq!(Attributes::from(e), open_init.clone().into())
                    }
                    IbcEvent::OpenTryChannel(e) => {
                        assert_eq!(Attributes::from(e), open_try.clone().into())
                    }
                    IbcEvent::OpenAckChannel(e) => {
                        assert_eq!(Attributes::from(e), open_ack.clone().into())
                    }
                    IbcEvent::OpenConfirmChannel(e) => {
                        assert_eq!(Attributes::from(e), open_confirm.clone().into())
                    }
                    IbcEvent::CloseInitChannel(e) => {
                        assert_eq!(Attributes::from(e), close_init.clone().into())
                    }
                    IbcEvent::CloseConfirmChannel(e) => {
                        assert_eq!(Attributes::from(e), close_confirm.clone().into())
                    }
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
            source_channel: "channel-0".parse().unwrap(),
            destination_port: "b_test_port".parse().unwrap(),
            destination_channel: "channel-1".parse().unwrap(),
            data: "test_data".as_bytes().to_vec(),
            timeout_height: Height::new(1, 10).unwrap().into(),
            timeout_timestamp: Timestamp::now(),
        };
        let mut abci_events = vec![];
        let send_packet = SendPacket {
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(send_packet.clone()).unwrap());
        let write_ack = WriteAcknowledgement {
            packet: packet.clone(),
            ack: "test_ack".as_bytes().to_vec(),
        };
        abci_events.push(AbciEvent::try_from(write_ack.clone()).unwrap());
        let ack_packet = AcknowledgePacket {
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(ack_packet.clone()).unwrap());
        let timeout_packet = TimeoutPacket { packet };
        abci_events.push(AbciEvent::try_from(timeout_packet.clone()).unwrap());

        for abci_event in abci_events {
            match IbcEvent::try_from(&abci_event).ok() {
                Some(ibc_event) => match ibc_event {
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
