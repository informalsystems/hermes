use alloc::collections::btree_map::BTreeMap as HashMap;

use ibc::core::ics02_client::height::HeightErrorDetail;
use ibc::core::ics04_channel::error::Error;
use ibc::core::ics04_channel::events::{
    AcknowledgePacket, Attributes, CloseConfirm, CloseInit, EventType, OpenAck, OpenConfirm,
    OpenInit, OpenTry, SendPacket, TimeoutPacket, WriteAcknowledgement, CHANNEL_ID_ATTRIBUTE_KEY,
    CONNECTION_ID_ATTRIBUTE_KEY, COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY,
    COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY, PKT_ACK_ATTRIBUTE_KEY, PKT_DATA_ATTRIBUTE_KEY,
    PKT_DST_CHANNEL_ATTRIBUTE_KEY, PKT_DST_PORT_ATTRIBUTE_KEY, PKT_SEQ_ATTRIBUTE_KEY,
    PKT_SRC_CHANNEL_ATTRIBUTE_KEY, PKT_SRC_PORT_ATTRIBUTE_KEY, PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY,
    PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY, PORT_ID_ATTRIBUTE_KEY,
};
use ibc::core::ics04_channel::events::{ReceivePacket, TimeoutOnClosePacket};
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::timeout::TimeoutHeight;
use ibc::events::{Error as EventError, IbcEvent, IbcEventType};
use ibc::Height;
use tendermint::abci::Event as AbciEvent;

pub fn try_from_tx(event: &AbciEvent) -> Option<IbcEvent> {
    match event.type_str.parse() {
        Ok(IbcEventType::OpenInitChannel) => extract_attributes_from_tx(event)
            .map(OpenInit::try_from)
            .map(|res| res.ok().map(IbcEvent::OpenInitChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::OpenTryChannel) => extract_attributes_from_tx(event)
            .map(OpenTry::try_from)
            .map(|res| res.ok().map(IbcEvent::OpenTryChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::OpenAckChannel) => extract_attributes_from_tx(event)
            .map(OpenAck::try_from)
            .map(|res| res.ok().map(IbcEvent::OpenAckChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::OpenConfirmChannel) => extract_attributes_from_tx(event)
            .map(OpenConfirm::try_from)
            .map(|res| res.ok().map(IbcEvent::OpenConfirmChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::CloseInitChannel) => extract_attributes_from_tx(event)
            .map(CloseInit::try_from)
            .map(|res| res.ok().map(IbcEvent::CloseInitChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::CloseConfirmChannel) => extract_attributes_from_tx(event)
            .map(CloseConfirm::try_from)
            .map(|res| res.ok().map(IbcEvent::CloseConfirmChannel))
            .ok()
            .flatten(),
        Ok(IbcEventType::SendPacket) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::SendPacket(SendPacket {
                        height: Height::new(0, 1).unwrap(),
                        packet,
                    })
                })
                .ok()
        }
        Ok(IbcEventType::WriteAck) => extract_packet_and_write_ack_from_tx(event)
            .map(|(packet, write_ack)| {
                IbcEvent::WriteAcknowledgement(WriteAcknowledgement {
                    height: Height::new(0, 1).unwrap(),
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
                        height: Height::new(0, 1).unwrap(),
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
                        height: Height::new(0, 1).unwrap(),
                        packet,
                    })
                })
                .ok()
        }
        _ => None,
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

fn extract_attributes(object: &RawObject<'_>, namespace: &str) -> Result<Attributes, EventError> {
    Ok(Attributes {
        height: object.height,
        port_id: extract_attribute(object, &format!("{}.port_id", namespace))?
            .parse()
            .map_err(EventError::parse)?,
        channel_id: maybe_extract_attribute(object, &format!("{}.channel_id", namespace))
            .and_then(|v| v.parse().ok()),
        connection_id: extract_attribute(object, &format!("{}.connection_id", namespace))?
            .parse()
            .map_err(EventError::parse)?,
        counterparty_port_id: extract_attribute(
            object,
            &format!("{}.counterparty_port_id", namespace),
        )?
        .parse()
        .map_err(EventError::parse)?,
        counterparty_channel_id: maybe_extract_attribute(
            object,
            &format!("{}.counterparty_channel_id", namespace),
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
                let height = obj.height;
                let data_str: String = extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_DATA_ATTRIBUTE_KEY))?;

                let mut packet = Packet::try_from(obj)?;
                packet.data = Vec::from(data_str.as_str().as_bytes());

                Ok(Self { height, packet })
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
        let height = obj.height;
        let data_str: String =
            extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_DATA_ATTRIBUTE_KEY))?;
        let ack = extract_attribute(&obj, &format!("{}.{}", obj.action, PKT_ACK_ATTRIBUTE_KEY))?
            .into_bytes();

        let mut packet = Packet::try_from(obj)?;
        packet.data = Vec::from(data_str.as_str().as_bytes());

        Ok(Self {
            height,
            packet,
            ack,
        })
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

#[cfg(test)]
mod tests {
    use ibc::core::ics04_channel::packet::Sequence;
    use ibc::timestamp::Timestamp;

    use super::*;

    #[test]
    fn channel_event_to_abci_event() {
        let attributes = Attributes {
            height: Height::new(0, 1).unwrap(),
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
            height: Height::new(0, 1).unwrap(),
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(send_packet.clone()).unwrap());
        let write_ack = WriteAcknowledgement {
            height: Height::new(0, 1).unwrap(),
            packet: packet.clone(),
            ack: "test_ack".as_bytes().to_vec(),
        };
        abci_events.push(AbciEvent::try_from(write_ack.clone()).unwrap());
        let ack_packet = AcknowledgePacket {
            height: Height::new(0, 1).unwrap(),
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(ack_packet.clone()).unwrap());
        let timeout_packet = TimeoutPacket {
            height: Height::new(0, 1).unwrap(),
            packet,
        };
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
