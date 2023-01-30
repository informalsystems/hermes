use alloc::collections::btree_map::BTreeMap as HashMap;

use ibc_relayer_types::core::ics02_client::height::HeightErrorDetail;
use ibc_relayer_types::core::ics04_channel::error::Error;
use ibc_relayer_types::core::ics04_channel::events::{
    AcknowledgePacket, Attributes, CloseConfirm, CloseInit, EventType, OpenAck, OpenConfirm,
    OpenInit, OpenTry, SendPacket, TimeoutPacket, WriteAcknowledgement, PKT_ACK_ATTRIBUTE_KEY,
    PKT_DATA_ATTRIBUTE_KEY, PKT_DST_CHANNEL_ATTRIBUTE_KEY, PKT_DST_PORT_ATTRIBUTE_KEY,
    PKT_SEQ_ATTRIBUTE_KEY, PKT_SRC_CHANNEL_ATTRIBUTE_KEY, PKT_SRC_PORT_ATTRIBUTE_KEY,
    PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY, PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY,
};
use ibc_relayer_types::core::ics04_channel::events::{ReceivePacket, TimeoutOnClosePacket};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::events::Error as EventError;
use ibc_relayer_types::Height;

fn extract_attributes(object: &RawObject<'_>, namespace: &str) -> Result<Attributes, EventError> {
    Ok(Attributes {
        port_id: extract_attribute(object, &format!("{namespace}.port_id"))?
            .parse()
            .map_err(EventError::parse)?,
        channel_id: maybe_extract_attribute(object, &format!("{namespace}.channel_id"))
            .and_then(|v| v.parse().ok()),
        connection_id: extract_attribute(object, &format!("{namespace}.connection_id"))?
            .parse()
            .map_err(EventError::parse)?,
        counterparty_port_id: extract_attribute(
            object,
            &format!("{namespace}.counterparty_port_id"),
        )?
        .parse()
        .map_err(EventError::parse)?,
        counterparty_channel_id: maybe_extract_attribute(
            object,
            &format!("{namespace}.counterparty_channel_id"),
        )
        .and_then(|v| v.parse().ok()),
    })
}

macro_rules! impl_try_from_raw_obj_for_event {
    ($($event:ty),+) => {
        $(impl TryFrom<RawObject<'_>> for $event {
            type Error = EventError;

            fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
                extract_attributes(&obj, Self::event_type().as_str())?.try_into()
            }
        })+
    };
}

impl_try_from_raw_obj_for_event!(
    OpenInit,
    OpenTry,
    OpenAck,
    OpenConfirm,
    CloseInit,
    CloseConfirm
);

macro_rules! impl_try_from_raw_obj_for_packet {
    ($($packet:ty),+) => {
        $(impl TryFrom<RawObject<'_>> for $packet {
            type Error = EventError;

            fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
                let data_str: String = extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_DATA_ATTRIBUTE_KEY))?;

                let mut packet = Packet::try_from(obj)?;
                packet.data = Vec::from(data_str.as_str().as_bytes());

                Ok(Self { packet })
            }
        })+
    };
}

impl_try_from_raw_obj_for_packet!(
    SendPacket,
    ReceivePacket,
    AcknowledgePacket,
    TimeoutPacket,
    TimeoutOnClosePacket
);

impl TryFrom<RawObject<'_>> for WriteAcknowledgement {
    type Error = EventError;

    fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
        let data_str: String =
            extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_DATA_ATTRIBUTE_KEY))?;
        let ack = extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_ACK_ATTRIBUTE_KEY))?
            .into_bytes();

        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());

        Ok(Self { packet, ack })
    }
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

impl TryFrom<RawObject<'_>> for Packet {
    type Error = EventError;
    fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
        Ok(Packet {
            sequence: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_SEQ_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::channel)?,
            source_port: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_SRC_PORT_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::parse)?,
            source_channel: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_SRC_CHANNEL_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::parse)?,
            destination_port: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_DST_PORT_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::parse)?,
            destination_channel: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_DST_CHANNEL_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::parse)?,
            data: vec![],
            timeout_height: {
                let timeout_height_str = extract_attribute(
                    &obj,
                    &format!("{}.{}", obj.action, PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY),
                )?;
                parse_timeout_height(&timeout_height_str).map_err(|_| EventError::height())?
            },
            timeout_timestamp: extract_attribute(
                &obj,
                &format!("{}.{}", obj.action, PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY),
            )?
            .parse()
            .map_err(EventError::timestamp)?,
        })
    }
}

#[derive(Debug, Clone)]
pub struct RawObject<'a> {
    pub height: Height,
    pub action: String,
    pub idx: usize,
    pub events: &'a HashMap<String, Vec<String>>,
}

impl<'a> RawObject<'a> {
    pub fn new(
        height: Height,
        action: String,
        idx: usize,
        events: &'a HashMap<String, Vec<String>>,
    ) -> RawObject<'a> {
        RawObject {
            height,
            action,
            idx,
            events,
        }
    }
}

pub fn extract_attribute(object: &RawObject<'_>, key: &str) -> Result<String, EventError> {
    let value = object
        .events
        .get(key)
        .ok_or_else(|| EventError::missing_key(key.to_string()))?[object.idx]
        .clone();

    Ok(value)
}

pub fn maybe_extract_attribute(object: &RawObject<'_>, key: &str) -> Option<String> {
    object.events.get(key).map(|tags| tags[object.idx].clone())
}
