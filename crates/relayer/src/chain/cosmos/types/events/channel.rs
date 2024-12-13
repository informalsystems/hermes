use alloc::collections::btree_map::BTreeMap as HashMap;

use ibc_relayer_types::applications::ics31_icq::events::CrossChainQueryPacket;
use ibc_relayer_types::core::ics02_client::height::HeightErrorDetail;
use ibc_relayer_types::core::ics04_channel::error::Error;
use ibc_relayer_types::core::ics04_channel::events::{
    AcknowledgePacket, Attributes, CloseConfirm, CloseInit, EventType, OpenAck, OpenConfirm,
    OpenInit, OpenTry, SendPacket, TimeoutPacket, UpgradeAttributes, UpgradeInit,
    WriteAcknowledgement, PKT_ACK_ATTRIBUTE_KEY, PKT_DATA_ATTRIBUTE_KEY,
    PKT_DST_CHANNEL_ATTRIBUTE_KEY, PKT_DST_PORT_ATTRIBUTE_KEY, PKT_SEQ_ATTRIBUTE_KEY,
    PKT_SRC_CHANNEL_ATTRIBUTE_KEY, PKT_SRC_PORT_ATTRIBUTE_KEY, PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY,
    PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY,
};
use ibc_relayer_types::core::ics04_channel::events::{ReceivePacket, TimeoutOnClosePacket};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
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

fn extract_upgrade_attributes(
    object: &RawObject<'_>,
    namespace: &str,
) -> Result<UpgradeAttributes, EventError> {
    Ok(UpgradeAttributes {
        port_id: extract_attribute(object, &format!("{namespace}.port_id"))?
            .parse()
            .map_err(EventError::parse)?,
        channel_id: extract_attribute(object, &format!("{namespace}.channel_id"))?
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
        upgrade_sequence: extract_attribute(object, &format!("{namespace}.upgrade_sequence"))?
            .parse()
            .map_err(|_| EventError::missing_action_string())?,
        upgrade_timeout_height: maybe_extract_attribute(
            object,
            &format!("{namespace}.timeout_height"),
        )
        .and_then(|v| v.parse().ok()),
        upgrade_timeout_timestamp: maybe_extract_attribute(
            object,
            &format!("{namespace}.timeout_timestamp"),
        )
        .and_then(|v| v.parse().ok()),
        error_receipt: maybe_extract_attribute(object, &format!("{namespace}.error_receipt"))
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
                let packet = Packet::try_from(obj)?;
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
        let ack_str =
            extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_ACK_ATTRIBUTE_KEY))?;

        let ack = hex::decode(ack_str.to_lowercase())
            .map_err(|_| EventError::invalid_packet_ack(ack_str))?;

        let packet = Packet::try_from(obj)?;

        Ok(Self { packet, ack })
    }
}

impl TryFrom<RawObject<'_>> for UpgradeInit {
    type Error = EventError;

    fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
        extract_upgrade_attributes(&obj, Self::event_type().as_str())?.try_into()
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
        let data_str =
            extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_DATA_ATTRIBUTE_KEY))?;

        let data = hex::decode(data_str.to_lowercase())
            .map_err(|_| EventError::invalid_packet_data(data_str))?;

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

            data,

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

impl TryFrom<RawObject<'_>> for CrossChainQueryPacket {
    type Error = EventError;

    fn try_from(obj: RawObject<'_>) -> Result<Self, Self::Error> {
        Ok(Self {
            module: extract_attribute(&obj, &format!("{}.module", obj.action))?,
            action: extract_attribute(&obj, &format!("{}.action", obj.action))?,
            query_id: extract_attribute(&obj, &format!("{}.query_id", obj.action))?,
            chain_id: extract_attribute(&obj, &format!("{}.chain_id", obj.action))
                .map(|s| ChainId::from_string(&s))?,
            connection_id: extract_attribute(&obj, &format!("{}.connection_id", obj.action))?
                .parse()
                .map_err(EventError::parse)?,
            query_type: extract_attribute(&obj, &format!("{}.type", obj.action))?,
            request: extract_attribute(&obj, &format!("{}.request", obj.action))?,
            height: extract_attribute(&obj, &format!("{}.height", obj.action))?
                .parse()
                .map_err(|_| EventError::height())?,
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
