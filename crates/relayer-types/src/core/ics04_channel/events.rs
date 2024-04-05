//! Types for the IBC events emitted from Tendermint Websocket by the channels module.

use std::fmt::{Display, Error as FmtError, Formatter};
use std::str;

use serde_derive::{Deserialize, Serialize};
use tendermint::abci;

use crate::core::ics02_client::height::Height;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::events::{Error as EventError, IbcEvent, IbcEventType};
use crate::timestamp::Timestamp;
use crate::utils::pretty::PrettySlice;

/// Channel event attribute keys
pub const CONNECTION_ID_ATTRIBUTE_KEY: &str = "connection_id";
pub const CHANNEL_ID_ATTRIBUTE_KEY: &str = "channel_id";
pub const PORT_ID_ATTRIBUTE_KEY: &str = "port_id";
pub const COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY: &str = "counterparty_channel_id";
pub const COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY: &str = "counterparty_port_id";

/// Packet event attribute keys
pub const PKT_SEQ_ATTRIBUTE_KEY: &str = "packet_sequence";
pub const PKT_DATA_ATTRIBUTE_KEY: &str = "packet_data_hex";
pub const PKT_SRC_PORT_ATTRIBUTE_KEY: &str = "packet_src_port";
pub const PKT_SRC_CHANNEL_ATTRIBUTE_KEY: &str = "packet_src_channel";
pub const PKT_DST_PORT_ATTRIBUTE_KEY: &str = "packet_dst_port";
pub const PKT_DST_CHANNEL_ATTRIBUTE_KEY: &str = "packet_dst_channel";
pub const PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY: &str = "packet_timeout_height";
pub const PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY: &str = "packet_timeout_timestamp";
pub const PKT_ACK_ATTRIBUTE_KEY: &str = "packet_ack_hex";

/// Channel upgrade attribute keys
pub const UPGRADE_SEQUENCE: &str = "upgrade_sequence";
pub const UPGRADE_TIMEOUT_HEIGHT: &str = "timeout_height";
pub const UPGRADE_TIMEOUT_TIMESTAMP: &str = "timeout_timestamp";
pub const UPGRADE_ERROR_RECEIPT: &str = "error_receipt";

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
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

impl Display for Attributes {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "Attributes {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "Attributes {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "Attributes {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "Attributes {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
}

/// Convert attributes to Tendermint ABCI tags
impl From<Attributes> for Vec<abci::EventAttribute> {
    fn from(a: Attributes) -> Self {
        let mut attributes = vec![];
        let port_id = (PORT_ID_ATTRIBUTE_KEY, a.port_id.as_str()).into();
        attributes.push(port_id);
        if let Some(channel_id) = a.channel_id {
            let channel_id = (CHANNEL_ID_ATTRIBUTE_KEY, channel_id.as_str()).into();
            attributes.push(channel_id);
        }
        let connection_id = (CONNECTION_ID_ATTRIBUTE_KEY, a.connection_id.as_str()).into();
        attributes.push(connection_id);
        let counterparty_port_id = (
            COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY,
            a.counterparty_port_id.as_str(),
        )
            .into();
        attributes.push(counterparty_port_id);
        if let Some(channel_id) = a.counterparty_channel_id {
            let channel_id = (COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY, channel_id.as_str()).into();
            attributes.push(channel_id);
        }
        attributes
    }
}

/// The attributes emitted by upon receiving a channel upgrade init message.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct UpgradeAttributes {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
    pub upgrade_timeout_height: Option<Height>,
    pub upgrade_timeout_timestamp: Option<Timestamp>,
    pub error_receipt: Option<String>,
}

impl UpgradeAttributes {
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }
}

impl Display for UpgradeAttributes {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}
pub trait EventType {
    fn event_type() -> IbcEventType;
}

/// Convert channel upgrade attributes to Tendermint ABCI tags
impl From<UpgradeAttributes> for Vec<abci::EventAttribute> {
    fn from(a: UpgradeAttributes) -> Self {
        let mut attributes: Vec<abci::EventAttribute> = vec![];

        let port_id: abci::EventAttribute = (PORT_ID_ATTRIBUTE_KEY, a.port_id.as_str()).into();
        attributes.push(port_id);

        let channel_id: abci::EventAttribute =
            (CHANNEL_ID_ATTRIBUTE_KEY, a.channel_id.as_str()).into();
        attributes.push(channel_id);

        let counterparty_port_id = (
            COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY,
            a.counterparty_port_id.as_str(),
        )
            .into();

        attributes.push(counterparty_port_id);
        let channel_id = (COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY, a.channel_id.as_str()).into();
        attributes.push(channel_id);

        let upgrade_sequence = (UPGRADE_SEQUENCE, a.upgrade_sequence.to_string().as_str()).into();
        attributes.push(upgrade_sequence);

        attributes
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for OpenInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "OpenInit {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "OpenInit {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "OpenInit {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "OpenInit {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenTry {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Display for OpenTry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "OpenTry {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "OpenTry {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "OpenTry {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "OpenTry {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenAck {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub counterparty_channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
}

impl Display for OpenAck {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "OpenAck {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "OpenAck {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "OpenAck {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "OpenAck {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenConfirm {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Display for OpenConfirm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "OpenConfirm {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "OpenConfirm {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "OpenConfirm {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "OpenConfirm {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CloseInit {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Display for CloseInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.counterparty_channel_id {
            Some(counterparty_channel_id) => write!(f, "CloseInit {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            None => write!(f, "CloseInit {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
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

impl From<CloseInit> for IbcEvent {
    fn from(v: CloseInit) -> Self {
        IbcEvent::CloseInitChannel(v)
    }
}

impl EventType for CloseInit {
    fn event_type() -> IbcEventType {
        IbcEventType::CloseInitChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CloseConfirm {
    pub channel_id: Option<ChannelId>,
    pub port_id: PortId,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Display for CloseConfirm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.channel_id, &self.counterparty_channel_id) {
            (Some(channel_id), Some(counterparty_channel_id)) => write!(f, "CloseConfirm {{ port_id: {}, channel_id: {}, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, channel_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (Some(channel_id), None) => write!(f, "CloseConfirm {{ port_id: {}, channel_id: {}, connection_id: None, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, channel_id, self.counterparty_port_id),
            (None, Some(counterparty_channel_id)) => write!(f, "CloseConfirm {{ port_id: {}, channel_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: {} }}", self.port_id, self.connection_id, self.counterparty_port_id, counterparty_channel_id),
            (None, None) => write!(f, "CloseConfirm {{ port_id: {}, client_id: None, connection_id: {}, counterparty_port_id: {}, counterparty_channel_id: None }}", self.port_id, self.connection_id, self.counterparty_port_id),
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeInit {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeInit> for UpgradeAttributes {
    fn from(ev: UpgradeInit) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeInit {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeInit {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeInit> for IbcEvent {
    fn from(v: UpgradeInit) -> Self {
        IbcEvent::UpgradeInitChannel(v)
    }
}

impl EventType for UpgradeInit {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeInitChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeTry {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeTry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeTry> for UpgradeAttributes {
    fn from(ev: UpgradeTry) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeTry {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeTry {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeTry> for IbcEvent {
    fn from(v: UpgradeTry) -> Self {
        IbcEvent::UpgradeTryChannel(v)
    }
}

impl EventType for UpgradeTry {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeTryChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeAck {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeAck {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeAck> for UpgradeAttributes {
    fn from(ev: UpgradeAck) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeAck {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeAck {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeAck> for IbcEvent {
    fn from(v: UpgradeAck) -> Self {
        IbcEvent::UpgradeAckChannel(v)
    }
}

impl EventType for UpgradeAck {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeAckChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeConfirm {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeConfirm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeConfirm> for UpgradeAttributes {
    fn from(ev: UpgradeConfirm) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeConfirm {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeConfirm {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeConfirm> for IbcEvent {
    fn from(v: UpgradeConfirm) -> Self {
        IbcEvent::UpgradeConfirmChannel(v)
    }
}

impl EventType for UpgradeConfirm {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeConfirmChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeOpen {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeOpen {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeOpen> for UpgradeAttributes {
    fn from(ev: UpgradeOpen) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeOpen {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeOpen {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeOpen> for IbcEvent {
    fn from(v: UpgradeOpen) -> Self {
        IbcEvent::UpgradeOpenChannel(v)
    }
}

impl EventType for UpgradeOpen {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeOpenChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeCancel {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
}

impl Display for UpgradeCancel {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }
        write!(f, "], upgrade_sequence: {} }}", self.upgrade_sequence)
    }
}

impl From<UpgradeCancel> for UpgradeAttributes {
    fn from(ev: UpgradeCancel) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: None,
        }
    }
}

impl UpgradeCancel {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeCancel {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
        })
    }
}

impl From<UpgradeCancel> for IbcEvent {
    fn from(v: UpgradeCancel) -> Self {
        IbcEvent::UpgradeCancelChannel(v)
    }
}

impl EventType for UpgradeCancel {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeCancelChannel
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeTimeout {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
    pub upgrade_timeout_height: Option<Height>,
    pub upgrade_timeout_timestamp: Option<Timestamp>,
}

impl Display for UpgradeTimeout {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }

        write!(f, "], upgrade_sequence: {}", self.upgrade_sequence)?;

        match (self.upgrade_timeout_height, self.upgrade_timeout_timestamp) {
            (Some(height), Some(timestamp)) => write!(
                f,
                " timeout_height: {}, timeout_timestamp: {} }}",
                height, timestamp
            ),
            (Some(height), None) => write!(f, " timeout_height: {} }}", height),
            (None, Some(timestamp)) => write!(f, " timeout_timestamp: {} }}", timestamp),
            (None, None) => write!(f, " }}"),
        }
    }
}

impl From<UpgradeTimeout> for UpgradeAttributes {
    fn from(ev: UpgradeTimeout) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: ev.upgrade_timeout_height,
            upgrade_timeout_timestamp: ev.upgrade_timeout_timestamp,
            error_receipt: None,
        }
    }
}

impl UpgradeTimeout {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeTimeout {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
            upgrade_timeout_height: attrs.upgrade_timeout_height,
            upgrade_timeout_timestamp: attrs.upgrade_timeout_timestamp,
        })
    }
}

impl From<UpgradeTimeout> for IbcEvent {
    fn from(v: UpgradeTimeout) -> Self {
        IbcEvent::UpgradeTimeoutChannel(v)
    }
}

impl EventType for UpgradeTimeout {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeTimeoutChannel
    }
}
//

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeError {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
    pub upgrade_sequence: Sequence,
    pub error_receipt: String,
}

impl Display for UpgradeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        if let Some(counterparty_channel_id) = &self.counterparty_channel_id {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: {counterparty_channel_id}, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        } else {
            write!(f, "UpgradeAttributes {{ port_id: {}, channel_id: {}, counterparty_port_id: {}, counterparty_channel_id: None, upgrade_connection_hops: [", self.port_id, self.channel_id, self.counterparty_port_id)?;
        }

        write!(
            f,
            "], upgrade_sequence: {}, error_receipt: {} }}",
            self.upgrade_sequence, self.error_receipt
        )
    }
}

impl From<UpgradeError> for UpgradeAttributes {
    fn from(ev: UpgradeError) -> Self {
        Self {
            port_id: ev.port_id,
            channel_id: ev.channel_id,
            counterparty_port_id: ev.counterparty_port_id,
            counterparty_channel_id: ev.counterparty_channel_id,
            upgrade_sequence: ev.upgrade_sequence,
            upgrade_timeout_height: None,
            upgrade_timeout_timestamp: None,
            error_receipt: Some(ev.error_receipt),
        }
    }
}

impl UpgradeError {
    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn counterparty_port_id(&self) -> &PortId {
        &self.counterparty_port_id
    }

    pub fn counterparty_channel_id(&self) -> Option<&ChannelId> {
        self.counterparty_channel_id.as_ref()
    }
}

impl TryFrom<UpgradeAttributes> for UpgradeError {
    type Error = EventError;

    fn try_from(attrs: UpgradeAttributes) -> Result<Self, Self::Error> {
        let error_receipt = attrs.error_receipt.unwrap_or_default();
        Ok(Self {
            port_id: attrs.port_id,
            channel_id: attrs.channel_id,
            counterparty_port_id: attrs.counterparty_port_id,
            counterparty_channel_id: attrs.counterparty_channel_id,
            upgrade_sequence: attrs.upgrade_sequence,
            error_receipt,
        })
    }
}

impl From<UpgradeError> for IbcEvent {
    fn from(v: UpgradeError) -> Self {
        IbcEvent::UpgradeErrorChannel(v)
    }
}

impl EventType for UpgradeError {
    fn event_type() -> IbcEventType {
        IbcEventType::UpgradeErrorChannel
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
        $(impl From<$event> for abci::Event {
            fn from(v: $event) -> Self {
                let kind = <$event>::event_type().as_str().to_owned();
                Self {
                    kind,
                    attributes: Attributes::from(v).into(),
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for SendPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "SendPacket {{ packet: {} }}", self.packet)
    }
}

impl From<SendPacket> for IbcEvent {
    fn from(v: SendPacket) -> Self {
        IbcEvent::SendPacket(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for ReceivePacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "ReceivePacket {{ packet: {} }}", self.packet)
    }
}

impl From<ReceivePacket> for IbcEvent {
    fn from(v: ReceivePacket) -> Self {
        IbcEvent::ReceivePacket(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for WriteAcknowledgement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "WriteAcknowledgement {{ packet: {}, ack: {} }}",
            self.packet,
            PrettySlice(&self.ack)
        )
    }
}

impl From<WriteAcknowledgement> for IbcEvent {
    fn from(v: WriteAcknowledgement) -> Self {
        IbcEvent::WriteAcknowledgement(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for AcknowledgePacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "AcknowledgePacket {{ packet: {}}}", self.packet)
    }
}

impl From<AcknowledgePacket> for IbcEvent {
    fn from(v: AcknowledgePacket) -> Self {
        IbcEvent::AcknowledgePacket(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for TimeoutPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "TimeoutPacket {{ packet: {}}}", self.packet)
    }
}

impl From<TimeoutPacket> for IbcEvent {
    fn from(v: TimeoutPacket) -> Self {
        IbcEvent::TimeoutPacket(v)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

impl Display for TimeoutOnClosePacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "TimeoutOnClosePacket {{ packet: {}}}", self.packet)
    }
}

impl From<TimeoutOnClosePacket> for IbcEvent {
    fn from(v: TimeoutOnClosePacket) -> Self {
        IbcEvent::TimeoutOnClosePacket(v)
    }
}
