use core::fmt::{Display, Error as FmtError, Formatter};
use ibc_relayer_types::{
    applications::ics29_fee::events::IncentivizedPacket,
    applications::ics31_icq::events::CrossChainQueryPacket,
    core::ics02_client::{
        error::Error as ClientError,
        events::{self as client_events, Attributes as ClientAttributes, HEADER_ATTRIBUTE_KEY},
        header::Header,
        height::HeightErrorDetail,
    },
    core::ics03_connection::{
        error::Error as ConnectionError,
        events::{self as connection_events, Attributes as ConnectionAttributes},
    },
    core::ics04_channel::{
        error::Error as ChannelError,
        events::{self as channel_events, Attributes as ChannelAttributes},
        packet::Packet,
        timeout::TimeoutHeight,
    },
    events::{Error as IbcEventError, IbcEvent, IbcEventType},
    Height,
};
use serde::Serialize;
use tendermint::abci::Event as AbciEvent;

use crate::light_client::decode_header;

pub mod bus;
pub mod monitor;
pub mod rpc;

#[derive(Clone, Debug, Serialize)]
pub struct IbcEventWithHeight {
    pub event: IbcEvent,
    pub height: Height,
}

impl IbcEventWithHeight {
    pub fn new(event: IbcEvent, height: Height) -> Self {
        Self { event, height }
    }

    pub fn with_height(self, height: Height) -> Self {
        Self {
            event: self.event,
            height,
        }
    }
}

impl Display for IbcEventWithHeight {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{} at height {}", self.event, self.height)
    }
}

/// Note: This function, as well as other helpers, are needed as a workaround to
/// Rust's orphan rule. That is, we want the AbciEvent -> IbcEvent to be defined
/// in the relayer crate, but can't because neither AbciEvent nor IbcEvent are
/// defined in this crate. Hence, we are forced to make an ad-hoc function for
/// it.
pub fn ibc_event_try_from_abci_event(abci_event: &AbciEvent) -> Result<IbcEvent, IbcEventError> {
    match abci_event.kind.parse() {
        Ok(IbcEventType::CreateClient) => Ok(IbcEvent::CreateClient(
            create_client_try_from_abci_event(abci_event).map_err(IbcEventError::client)?,
        )),
        Ok(IbcEventType::UpdateClient) => Ok(IbcEvent::UpdateClient(
            update_client_try_from_abci_event(abci_event).map_err(IbcEventError::client)?,
        )),
        Ok(IbcEventType::UpgradeClient) => Ok(IbcEvent::UpgradeClient(
            upgrade_client_try_from_abci_event(abci_event).map_err(IbcEventError::client)?,
        )),
        Ok(IbcEventType::ClientMisbehaviour) => Ok(IbcEvent::ClientMisbehaviour(
            client_misbehaviour_try_from_abci_event(abci_event).map_err(IbcEventError::client)?,
        )),
        Ok(IbcEventType::OpenInitConnection) => Ok(IbcEvent::OpenInitConnection(
            connection_open_init_try_from_abci_event(abci_event)
                .map_err(IbcEventError::connection)?,
        )),
        Ok(IbcEventType::OpenTryConnection) => Ok(IbcEvent::OpenTryConnection(
            connection_open_try_try_from_abci_event(abci_event)
                .map_err(IbcEventError::connection)?,
        )),
        Ok(IbcEventType::OpenAckConnection) => Ok(IbcEvent::OpenAckConnection(
            connection_open_ack_try_from_abci_event(abci_event)
                .map_err(IbcEventError::connection)?,
        )),
        Ok(IbcEventType::OpenConfirmConnection) => Ok(IbcEvent::OpenConfirmConnection(
            connection_open_confirm_try_from_abci_event(abci_event)
                .map_err(IbcEventError::connection)?,
        )),
        Ok(IbcEventType::OpenInitChannel) => Ok(IbcEvent::OpenInitChannel(
            channel_open_init_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::OpenTryChannel) => Ok(IbcEvent::OpenTryChannel(
            channel_open_try_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::OpenAckChannel) => Ok(IbcEvent::OpenAckChannel(
            channel_open_ack_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::OpenConfirmChannel) => Ok(IbcEvent::OpenConfirmChannel(
            channel_open_confirm_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::CloseInitChannel) => Ok(IbcEvent::CloseInitChannel(
            channel_close_init_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::CloseConfirmChannel) => Ok(IbcEvent::CloseConfirmChannel(
            channel_close_confirm_try_from_abci_event(abci_event)
                .map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::SendPacket) => Ok(IbcEvent::SendPacket(
            send_packet_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::WriteAck) => Ok(IbcEvent::WriteAcknowledgement(
            write_acknowledgement_try_from_abci_event(abci_event)
                .map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::AckPacket) => Ok(IbcEvent::AcknowledgePacket(
            acknowledge_packet_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::Timeout) => Ok(IbcEvent::TimeoutPacket(
            timeout_packet_try_from_abci_event(abci_event).map_err(IbcEventError::channel)?,
        )),
        Ok(IbcEventType::IncentivizedPacket) => Ok(IbcEvent::IncentivizedPacket(
            IncentivizedPacket::try_from(&abci_event.attributes[..]).map_err(IbcEventError::fee)?,
        )),
        Ok(IbcEventType::CrossChainQuery) => Ok(IbcEvent::CrossChainQueryPacket(
            CrossChainQueryPacket::try_from(&abci_event.attributes[..])
                .map_err(IbcEventError::cross_chain_query)?,
        )),
        _ => Err(IbcEventError::unsupported_abci_event(
            abci_event.kind.clone(),
        )),
    }
}

pub fn create_client_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<client_events::CreateClient, ClientError> {
    client_extract_attributes_from_tx(abci_event).map(client_events::CreateClient)
}

pub fn update_client_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<client_events::UpdateClient, ClientError> {
    client_extract_attributes_from_tx(abci_event).map(|attributes| client_events::UpdateClient {
        common: attributes,
        header: extract_header_from_tx(abci_event).ok(),
    })
}

pub fn upgrade_client_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<client_events::UpgradeClient, ClientError> {
    client_extract_attributes_from_tx(abci_event).map(client_events::UpgradeClient)
}

pub fn client_misbehaviour_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<client_events::ClientMisbehaviour, ClientError> {
    client_extract_attributes_from_tx(abci_event).map(client_events::ClientMisbehaviour)
}

pub fn connection_open_init_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<connection_events::OpenInit, ConnectionError> {
    connection_extract_attributes_from_tx(abci_event).map(connection_events::OpenInit)
}

pub fn connection_open_try_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<connection_events::OpenTry, ConnectionError> {
    connection_extract_attributes_from_tx(abci_event).map(connection_events::OpenTry)
}

pub fn connection_open_ack_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<connection_events::OpenAck, ConnectionError> {
    connection_extract_attributes_from_tx(abci_event).map(connection_events::OpenAck)
}

pub fn connection_open_confirm_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<connection_events::OpenConfirm, ConnectionError> {
    connection_extract_attributes_from_tx(abci_event).map(connection_events::OpenConfirm)
}

pub fn channel_open_init_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::OpenInit, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::OpenInit::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn channel_open_try_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::OpenTry, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::OpenTry::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn channel_open_ack_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::OpenAck, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::OpenAck::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn channel_open_confirm_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::OpenConfirm, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::OpenConfirm::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn channel_close_init_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::CloseInit, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::CloseInit::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn channel_close_confirm_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::CloseConfirm, ChannelError> {
    match channel_extract_attributes_from_tx(abci_event) {
        Ok(attrs) => channel_events::CloseConfirm::try_from(attrs)
            .map_err(|_| ChannelError::implementation_specific()),
        Err(e) => Err(e),
    }
}

pub fn send_packet_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::SendPacket, ChannelError> {
    extract_packet_and_write_ack_from_tx(abci_event)
        .map(|(packet, write_ack)| {
            // This event should not have a write ack.
            debug_assert_eq!(write_ack.len(), 0);
            channel_events::SendPacket { packet }
        })
        .map_err(|_| ChannelError::abci_conversion_failed(abci_event.kind.clone()))
}

pub fn write_acknowledgement_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::WriteAcknowledgement, ChannelError> {
    extract_packet_and_write_ack_from_tx(abci_event)
        .map(|(packet, write_ack)| channel_events::WriteAcknowledgement {
            packet,
            ack: write_ack,
        })
        .map_err(|_| ChannelError::abci_conversion_failed(abci_event.kind.clone()))
}

pub fn acknowledge_packet_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::AcknowledgePacket, ChannelError> {
    extract_packet_and_write_ack_from_tx(abci_event)
        .map(|(packet, write_ack)| {
            // This event should not have a write ack.
            debug_assert_eq!(write_ack.len(), 0);
            channel_events::AcknowledgePacket { packet }
        })
        .map_err(|_| ChannelError::abci_conversion_failed(abci_event.kind.clone()))
}

pub fn timeout_packet_try_from_abci_event(
    abci_event: &AbciEvent,
) -> Result<channel_events::TimeoutPacket, ChannelError> {
    extract_packet_and_write_ack_from_tx(abci_event)
        .map(|(packet, write_ack)| {
            // This event should not have a write ack.
            debug_assert_eq!(write_ack.len(), 0);
            channel_events::TimeoutPacket { packet }
        })
        .map_err(|_| ChannelError::abci_conversion_failed(abci_event.kind.clone()))
}

fn client_extract_attributes_from_tx(event: &AbciEvent) -> Result<ClientAttributes, ClientError> {
    let mut attr = ClientAttributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_str();
        let value = tag.value.as_str();
        match key {
            client_events::CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value
                    .parse()
                    .map_err(ClientError::invalid_client_identifier)?
            }
            client_events::CLIENT_TYPE_ATTRIBUTE_KEY => {
                attr.client_type = value
                    .parse()
                    .map_err(|_| ClientError::unknown_client_type(value.to_string()))?
            }
            client_events::CONSENSUS_HEIGHT_ATTRIBUTE_KEY => {
                attr.consensus_height = value
                    .parse()
                    .map_err(|e| ClientError::invalid_string_as_height(value.to_string(), e))?
            }
            _ => {}
        }
    }

    Ok(attr)
}

pub fn extract_header_from_tx(event: &AbciEvent) -> Result<Box<dyn Header>, ClientError> {
    for tag in &event.attributes {
        if tag.key == HEADER_ATTRIBUTE_KEY {
            let header_bytes =
                hex::decode(&tag.value).map_err(|_| ClientError::malformed_header())?;
            return decode_header(&header_bytes);
        }
    }
    Err(ClientError::missing_raw_header())
}

fn connection_extract_attributes_from_tx(
    event: &AbciEvent,
) -> Result<ConnectionAttributes, ConnectionError> {
    let mut attr = ConnectionAttributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_str();
        let value = tag.value.as_str();
        match key {
            connection_events::CONN_ID_ATTRIBUTE_KEY => {
                attr.connection_id = value.parse().ok();
            }
            connection_events::CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value.parse().map_err(ConnectionError::invalid_identifier)?;
            }
            connection_events::COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY => {
                attr.counterparty_connection_id = value.parse().ok();
            }
            connection_events::COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_client_id =
                    value.parse().map_err(ConnectionError::invalid_identifier)?;
            }
            _ => {}
        }
    }

    Ok(attr)
}

fn channel_extract_attributes_from_tx(
    event: &AbciEvent,
) -> Result<ChannelAttributes, ChannelError> {
    let mut attr = ChannelAttributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_str();
        let value = tag.value.as_str();
        match key {
            channel_events::PORT_ID_ATTRIBUTE_KEY => {
                attr.port_id = value.parse().map_err(ChannelError::identifier)?
            }
            channel_events::CHANNEL_ID_ATTRIBUTE_KEY => {
                attr.channel_id = value.parse().ok();
            }
            channel_events::CONNECTION_ID_ATTRIBUTE_KEY => {
                attr.connection_id = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::COUNTERPARTY_PORT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_port_id = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::COUNTERPARTY_CHANNEL_ID_ATTRIBUTE_KEY => {
                attr.counterparty_channel_id = value.parse().ok();
            }
            _ => {}
        }
    }

    Ok(attr)
}

fn extract_packet_and_write_ack_from_tx(
    event: &AbciEvent,
) -> Result<(Packet, Vec<u8>), ChannelError> {
    let mut packet = Packet::default();
    let mut write_ack: Vec<u8> = Vec::new();
    for tag in &event.attributes {
        let key = tag.key.as_str();
        let value = tag.value.as_str();
        match key {
            channel_events::PKT_SRC_PORT_ATTRIBUTE_KEY => {
                packet.source_port = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::PKT_SRC_CHANNEL_ATTRIBUTE_KEY => {
                packet.source_channel = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::PKT_DST_PORT_ATTRIBUTE_KEY => {
                packet.destination_port = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::PKT_DST_CHANNEL_ATTRIBUTE_KEY => {
                packet.destination_channel = value.parse().map_err(ChannelError::identifier)?;
            }
            channel_events::PKT_SEQ_ATTRIBUTE_KEY => {
                packet.sequence = value
                    .parse::<u64>()
                    .map_err(|e| ChannelError::invalid_string_as_sequence(value.to_string(), e))?
                    .into()
            }
            channel_events::PKT_TIMEOUT_HEIGHT_ATTRIBUTE_KEY => {
                packet.timeout_height = parse_timeout_height(value)?;
            }
            channel_events::PKT_TIMEOUT_TIMESTAMP_ATTRIBUTE_KEY => {
                packet.timeout_timestamp = value.parse().unwrap();
            }
            channel_events::PKT_DATA_ATTRIBUTE_KEY => {
                packet.data = Vec::from(value.as_bytes());
            }
            channel_events::PKT_ACK_ATTRIBUTE_KEY => {
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
pub fn parse_timeout_height(s: &str) -> Result<TimeoutHeight, ChannelError> {
    match s.parse::<Height>() {
        Ok(height) => Ok(TimeoutHeight::from(height)),
        Err(e) => match e.into_detail() {
            HeightErrorDetail::ZeroHeight(_) => Ok(TimeoutHeight::no_timeout()),
            _ => Err(ChannelError::invalid_timeout_height()),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ibc_proto::google::protobuf::Any;
    use ibc_proto::protobuf::Protobuf;
    use ibc_relayer_types::clients::ics07_tendermint::header::test_util::get_dummy_ics07_header;
    use ibc_relayer_types::clients::ics07_tendermint::header::Header as TmHeader;
    use ibc_relayer_types::core::ics02_client::header::downcast_header;
    use ibc_relayer_types::core::ics04_channel::packet::Sequence;
    use ibc_relayer_types::timestamp::Timestamp;

    #[test]
    fn extract_header() {
        let header = get_dummy_ics07_header();
        let mut header_bytes = Vec::new();
        Protobuf::<Any>::encode(&header, &mut header_bytes).unwrap();

        let decoded_dyn_header = decode_header(&header_bytes).unwrap();
        let decoded_tm_header: &TmHeader = downcast_header(decoded_dyn_header.as_ref()).unwrap();

        assert_eq!(&header, decoded_tm_header);
    }

    #[test]
    fn connection_event_to_abci_event() {
        let attributes = ConnectionAttributes {
            connection_id: Some("test_connection".parse().unwrap()),
            client_id: "test_client".parse().unwrap(),
            counterparty_connection_id: Some("counterparty_test_conn".parse().unwrap()),
            counterparty_client_id: "counterparty_test_client".parse().unwrap(),
        };
        let mut abci_events = vec![];
        let open_init = connection_events::OpenInit::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = connection_events::OpenTry::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = connection_events::OpenAck::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = connection_events::OpenConfirm::from(attributes);
        abci_events.push(AbciEvent::from(open_confirm.clone()));

        for abci_event in abci_events {
            match ibc_event_try_from_abci_event(&abci_event).ok() {
                Some(ibc_event) => match ibc_event {
                    IbcEvent::OpenInitConnection(e) => assert_eq!(e, open_init),
                    IbcEvent::OpenTryConnection(e) => assert_eq!(e, open_try),
                    IbcEvent::OpenAckConnection(e) => assert_eq!(e, open_ack),
                    IbcEvent::OpenConfirmConnection(e) => assert_eq!(e, open_confirm),
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }

    #[test]
    fn channel_event_to_abci_event() {
        let attributes = ChannelAttributes {
            port_id: "test_port".parse().unwrap(),
            channel_id: Some("channel-0".parse().unwrap()),
            connection_id: "test_connection".parse().unwrap(),
            counterparty_port_id: "counterparty_test_port".parse().unwrap(),
            counterparty_channel_id: Some("channel-1".parse().unwrap()),
        };
        let mut abci_events = vec![];
        let open_init = channel_events::OpenInit::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = channel_events::OpenTry::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = channel_events::OpenAck::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = channel_events::OpenConfirm::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(open_confirm.clone()));
        let close_init = channel_events::CloseInit::try_from(attributes.clone()).unwrap();
        abci_events.push(AbciEvent::from(close_init.clone()));
        let close_confirm = channel_events::CloseConfirm::try_from(attributes).unwrap();
        abci_events.push(AbciEvent::from(close_confirm.clone()));

        for abci_event in abci_events {
            match ibc_event_try_from_abci_event(&abci_event).ok() {
                Some(ibc_event) => match ibc_event {
                    IbcEvent::OpenInitChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), open_init.clone().into())
                    }
                    IbcEvent::OpenTryChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), open_try.clone().into())
                    }
                    IbcEvent::OpenAckChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), open_ack.clone().into())
                    }
                    IbcEvent::OpenConfirmChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), open_confirm.clone().into())
                    }
                    IbcEvent::CloseInitChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), close_init.clone().into())
                    }
                    IbcEvent::CloseConfirmChannel(e) => {
                        assert_eq!(ChannelAttributes::from(e), close_confirm.clone().into())
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
        let send_packet = channel_events::SendPacket {
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(send_packet.clone()).unwrap());
        let write_ack = channel_events::WriteAcknowledgement {
            packet: packet.clone(),
            ack: "test_ack".as_bytes().to_vec(),
        };
        abci_events.push(AbciEvent::try_from(write_ack.clone()).unwrap());
        let ack_packet = channel_events::AcknowledgePacket {
            packet: packet.clone(),
        };
        abci_events.push(AbciEvent::try_from(ack_packet.clone()).unwrap());
        let timeout_packet = channel_events::TimeoutPacket { packet };
        abci_events.push(AbciEvent::try_from(timeout_packet.clone()).unwrap());

        for abci_event in abci_events {
            match ibc_event_try_from_abci_event(&abci_event).ok() {
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
