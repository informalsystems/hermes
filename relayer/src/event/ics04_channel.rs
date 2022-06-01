//! ABCI event parsing for the IBC events emitted from Tendermint Websocket by the channels module.

use tendermint_rpc::abci::Event as AbciEvent;

use ibc::core::ics04_channel::error::Error;
use ibc::core::ics04_channel::events::{
    AcknowledgePacket, Attributes, CloseConfirm, CloseInit, OpenAck, OpenConfirm, OpenInit,
    OpenTry, ReceivePacket, SendPacket, TimeoutOnClosePacket, TimeoutPacket, WriteAcknowledgement,
};
use ibc::core::ics04_channel::packet::Packet;
use ibc::events::{IbcEvent, IbcEventType};

/// Channel event attribute keys
#[cfg(test)]
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
                        height: Default::default(),
                        packet,
                    })
                })
                .ok()
        }
        Ok(IbcEventType::ReceivePacket) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::ReceivePacket(ReceivePacket {
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
        Ok(IbcEventType::TimeoutOnClose) => {
            extract_packet_and_write_ack_from_tx(event)
                .map(|(packet, write_ack)| {
                    // This event should not have a write ack.
                    debug_assert_eq!(write_ack.len(), 0);
                    IbcEvent::TimeoutOnClosePacket(TimeoutOnClosePacket {
                        height: Default::default(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::ToAbciEvent;
    use ibc::core::ics02_client::height::Height;
    use ibc::core::ics04_channel::packet::Sequence;
    use ibc::timestamp::Timestamp;
    use std::str;
    use tendermint_rpc::abci::tag::Tag;

    /// Convert attributes to Tendermint ABCI tags
    ///
    /// # Note
    /// The parsing of `Key`s and `Value`s never fails, because the
    /// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
    /// is infallible, even if it is not represented in the error type.
    /// Once tendermint-rs improves the API of the `Key` and `Value` types,
    /// we will be able to remove the `.parse().unwrap()` calls.
    fn attributes_to_abci_tags(a: &Attributes) -> Vec<Tag> {
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

    /// Convert packet data to Tendermint ABCI tags
    ///
    /// # Note
    /// The parsing of `Key`s and `Value`s never fails, because the
    /// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
    /// is infallible, even if it is not represented in the error type.
    /// Once tendermint-rs improves the API of the `Key` and `Value` types,
    /// we will be able to remove the `.parse().unwrap()` calls.
    fn packet_to_abci_tags(p: &Packet) -> Vec<Tag> {
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
                .nanoseconds()
                .to_string()
                .parse()
                .unwrap(),
        };
        attributes.push(timeout_timestamp);
        let val = str::from_utf8(&p.data).expect("hex-encoded string should always be valid UTF-8");
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
        attributes
    }

    macro_rules! impl_to_abci_event {
        ($event:ty, $event_type:expr) => {
            impl ToAbciEvent for $event {
                fn to_abci_event(&self) -> AbciEvent {
                    let attributes = attributes_to_abci_tags(&self.clone().into());
                    let type_str = $event_type.as_str().to_string();
                    AbciEvent {
                        type_str,
                        attributes,
                    }
                }
            }
        };
    }

    impl_to_abci_event!(OpenInit, IbcEventType::OpenInitChannel);
    impl_to_abci_event!(OpenTry, IbcEventType::OpenTryChannel);
    impl_to_abci_event!(OpenAck, IbcEventType::OpenAckChannel);
    impl_to_abci_event!(OpenConfirm, IbcEventType::OpenConfirmChannel);
    impl_to_abci_event!(CloseInit, IbcEventType::CloseInitChannel);
    impl_to_abci_event!(CloseConfirm, IbcEventType::CloseConfirmChannel);

    impl ToAbciEvent for SendPacket {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = packet_to_abci_tags(&self.packet);
            AbciEvent {
                type_str: IbcEventType::SendPacket.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for ReceivePacket {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = packet_to_abci_tags(&self.packet);
            AbciEvent {
                type_str: IbcEventType::ReceivePacket.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for WriteAcknowledgement {
        fn to_abci_event(&self) -> AbciEvent {
            let mut attributes = packet_to_abci_tags(&self.packet);
            let val = String::from_utf8(self.ack.to_vec())
                .expect("hex-encoded string should always be valid UTF-8");
            // No actual conversion from string to `Tag::Key` or `Tag::Value`
            let ack = Tag {
                key: PKT_ACK_ATTRIBUTE_KEY.parse().unwrap(),
                value: val.parse().unwrap(),
            };
            attributes.push(ack);
            AbciEvent {
                type_str: IbcEventType::WriteAck.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for AcknowledgePacket {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = packet_to_abci_tags(&self.packet);
            AbciEvent {
                type_str: IbcEventType::AckPacket.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for TimeoutPacket {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = packet_to_abci_tags(&self.packet);
            AbciEvent {
                type_str: IbcEventType::Timeout.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for TimeoutOnClosePacket {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = packet_to_abci_tags(&self.packet);
            AbciEvent {
                type_str: IbcEventType::TimeoutOnClose.as_str().to_string(),
                attributes,
            }
        }
    }

    #[test]
    fn channel_event_to_abci_event() {
        let attributes = Attributes {
            height: Height::default(),
            port_id: "test_port".parse().unwrap(),
            channel_id: Some("channel-0".parse().unwrap()),
            connection_id: "test_connection".parse().unwrap(),
            counterparty_port_id: "counterparty_test_port".parse().unwrap(),
            counterparty_channel_id: Some("channel-1".parse().unwrap()),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::try_from(attributes.clone()).unwrap();
        abci_events.push(open_init.to_abci_event());
        let open_try = OpenTry::try_from(attributes.clone()).unwrap();
        abci_events.push(open_try.to_abci_event());
        let open_ack = OpenAck::try_from(attributes.clone()).unwrap();
        abci_events.push(open_ack.to_abci_event());
        let open_confirm = OpenConfirm::try_from(attributes.clone()).unwrap();
        abci_events.push(open_confirm.to_abci_event());
        let close_init = CloseInit::try_from(attributes.clone()).unwrap();
        abci_events.push(close_init.to_abci_event());
        let close_confirm = CloseConfirm::try_from(attributes).unwrap();
        abci_events.push(close_confirm.to_abci_event());

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
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
            timeout_height: Height::new(1, 10),
            timeout_timestamp: Timestamp::now(),
        };
        let mut abci_events = vec![];
        let send_packet = SendPacket {
            height: Height::default(),
            packet: packet.clone(),
        };
        abci_events.push(send_packet.to_abci_event());
        let write_ack = WriteAcknowledgement {
            height: Height::default(),
            packet: packet.clone(),
            ack: "test_ack".as_bytes().to_vec(),
        };
        abci_events.push(write_ack.to_abci_event());
        let ack_packet = AcknowledgePacket {
            height: Height::default(),
            packet: packet.clone(),
        };
        abci_events.push(ack_packet.to_abci_event());
        let timeout_packet = TimeoutPacket {
            height: Height::default(),
            packet,
        };
        abci_events.push(timeout_packet.to_abci_event());

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
