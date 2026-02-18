//! Event parsing for Cardano Gateway events -> Hermes `IbcEvent` conversion.
//!
//! The Gateway returns events in the format:
//! `Event { type: "create_client", attributes: [{ key: "client_id", value: "08-cardano-0" }, ...] }`
//!
//! This module converts them into Hermes' `IbcEvent` enum variants.

use ibc_relayer_types::{
    core::{
        ics02_client::{
            events as ClientEvents,
            height::{Height, HeightErrorDetail},
        },
        ics03_connection::events as ConnectionEvents,
        ics04_channel::{events as ChannelEvents, packet::Packet, timeout::TimeoutHeight},
        ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
    },
    events::IbcEvent,
    timestamp::Timestamp,
};
use std::collections::HashMap;
use std::str::FromStr;

use super::error::Error;
use super::generated::ibc::cardano::v1::{Event, EventAttribute};

/// Parse a list of Gateway events into Hermes IbcEvent types
pub fn parse_events(gateway_events: Vec<Event>, _height: Height) -> Result<Vec<IbcEvent>, Error> {
    let event_count = gateway_events.len();
    tracing::debug!("Parsing {} gateway events", event_count);

    let mut ibc_events = Vec::new();
    let mut parsed_type_counts: HashMap<String, usize> = HashMap::new();
    let mut unknown_event_count = 0usize;

    for event in gateway_events {
        let event_type = event.r#type.clone();
        let attribute_count = event.attributes.len();
        let attributes = event.attributes.clone();
        let attrs = attributes_to_map(event.attributes);

        tracing::debug!(
            "Parsing event type: {} ({} attributes)",
            event_type,
            attribute_count
        );

        // Parse event based on type
        let ibc_event = match event_type.as_str() {
            // Client events
            "create_client" => parse_event_with_context(
                "create_client",
                &attributes,
                attrs,
                parse_create_client_event,
            )?,
            "update_client" => parse_event_with_context(
                "update_client",
                &attributes,
                attrs,
                parse_update_client_event,
            )?,
            "upgrade_client" => parse_event_with_context(
                "upgrade_client",
                &attributes,
                attrs,
                parse_upgrade_client_event,
            )?,
            "client_misbehaviour" => parse_event_with_context(
                "client_misbehaviour",
                &attributes,
                attrs,
                parse_client_misbehaviour_event,
            )?,

            // Connection events
            "connection_open_init" => parse_event_with_context(
                "connection_open_init",
                &attributes,
                attrs,
                parse_connection_open_init_event,
            )?,
            "connection_open_try" => parse_event_with_context(
                "connection_open_try",
                &attributes,
                attrs,
                parse_connection_open_try_event,
            )?,
            "connection_open_ack" => parse_event_with_context(
                "connection_open_ack",
                &attributes,
                attrs,
                parse_connection_open_ack_event,
            )?,
            "connection_open_confirm" => parse_event_with_context(
                "connection_open_confirm",
                &attributes,
                attrs,
                parse_connection_open_confirm_event,
            )?,

            // Channel events
            "channel_open_init" => parse_event_with_context(
                "channel_open_init",
                &attributes,
                attrs,
                parse_channel_open_init_event,
            )?,
            "channel_open_try" => parse_event_with_context(
                "channel_open_try",
                &attributes,
                attrs,
                parse_channel_open_try_event,
            )?,
            "channel_open_ack" => parse_event_with_context(
                "channel_open_ack",
                &attributes,
                attrs,
                parse_channel_open_ack_event,
            )?,
            "channel_open_confirm" => parse_event_with_context(
                "channel_open_confirm",
                &attributes,
                attrs,
                parse_channel_open_confirm_event,
            )?,
            "channel_close_init" => parse_event_with_context(
                "channel_close_init",
                &attributes,
                attrs,
                parse_channel_close_init_event,
            )?,
            "channel_close_confirm" => parse_event_with_context(
                "channel_close_confirm",
                &attributes,
                attrs,
                parse_channel_close_confirm_event,
            )?,

            // Packet events
            "send_packet" => parse_event_with_context(
                "send_packet",
                &attributes,
                attrs,
                parse_send_packet_event,
            )?,
            "recv_packet" => parse_event_with_context(
                "recv_packet",
                &attributes,
                attrs,
                parse_recv_packet_event,
            )?,
            "write_acknowledgement" => parse_event_with_context(
                "write_acknowledgement",
                &attributes,
                attrs,
                parse_write_acknowledgement_event,
            )?,
            "acknowledge_packet" => parse_event_with_context(
                "acknowledge_packet",
                &attributes,
                attrs,
                parse_acknowledge_packet_event,
            )?,
            "timeout_packet" => parse_event_with_context(
                "timeout_packet",
                &attributes,
                attrs,
                parse_timeout_packet_event,
            )?,
            "timeout_on_close_packet" => parse_event_with_context(
                "timeout_on_close_packet",
                &attributes,
                attrs,
                parse_timeout_on_close_packet_event,
            )?,

            // Unknown event type - log warning and skip
            _ => {
                let keys = attributes
                    .iter()
                    .map(|attr| attr.key.as_str())
                    .collect::<Vec<_>>();
                tracing::warn!(
                    "Unknown event type: {}; attribute keys: {:?}",
                    event_type,
                    keys
                );
                unknown_event_count += 1;
                continue;
            }
        };

        ibc_events.push(ibc_event);
        *parsed_type_counts.entry(event_type.clone()).or_default() += 1;
        tracing::debug!("Parsed event type: {}", event_type);
    }

    tracing::debug!(
        "Parsed {} of {} gateway events into IBC events",
        ibc_events.len(),
        event_count
    );

    if ibc_events.is_empty() && event_count > 0 {
        tracing::warn!("No events could be parsed from gateway response");
    }

    if !parsed_type_counts.is_empty() {
        tracing::debug!(
            "Parsed event counts by gateway type: {:?}",
            parsed_type_counts
        );
    }

    if unknown_event_count > 0 {
        tracing::warn!(
            "{} gateway events were ignored because event type was unknown",
            unknown_event_count
        );
    }

    Ok(ibc_events)
}

fn parse_event_with_context(
    event_type: &str,
    raw_attributes: &[EventAttribute],
    attrs: HashMap<String, String>,
    parser: impl FnOnce(HashMap<String, String>) -> Result<IbcEvent, Error>,
) -> Result<IbcEvent, Error> {
    match parser(attrs) {
        Ok(event) => Ok(event),
        Err(error) => {
            let keys = raw_attributes
                .iter()
                .map(|attribute| attribute.key.as_str())
                .collect::<Vec<_>>();

            tracing::warn!(
                "Failed to parse gateway event '{}'; attribute keys {:?}; error: {}",
                event_type,
                keys,
                error
            );

            Err(error)
        }
    }
}

/// Convert event attributes to a HashMap for easier lookup
fn attributes_to_map(attributes: Vec<EventAttribute>) -> HashMap<String, String> {
    attributes
        .into_iter()
        .map(|attr| (attr.key, attr.value))
        .collect()
}

//
// Client event parsers
//

fn parse_create_client_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let client_id = parse_client_id(&attrs, "client_id")?;
    let client_type = parse_client_type(&attrs, "client_type")?;
    let consensus_height = parse_height(&attrs, "consensus_height")?;

    let attributes = ClientEvents::Attributes {
        client_id,
        client_type,
        consensus_height,
    };

    Ok(IbcEvent::CreateClient(ClientEvents::CreateClient(
        attributes,
    )))
}

fn parse_update_client_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let client_id = parse_client_id(&attrs, "client_id")?;
    let client_type = parse_client_type(&attrs, "client_type")?;
    let consensus_height = parse_height(&attrs, "consensus_height")?;

    let common = ClientEvents::Attributes {
        client_id,
        client_type,
        consensus_height,
    };

    Ok(IbcEvent::UpdateClient(ClientEvents::UpdateClient {
        common,
        header: None, // Header is not included in Gateway events
    }))
}

fn parse_upgrade_client_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let client_id = parse_client_id(&attrs, "client_id")?;
    let client_type = parse_client_type(&attrs, "client_type")?;
    let consensus_height = parse_height(&attrs, "consensus_height")?;

    let attributes = ClientEvents::Attributes {
        client_id,
        client_type,
        consensus_height,
    };

    Ok(IbcEvent::UpgradeClient(ClientEvents::UpgradeClient(
        attributes,
    )))
}

fn parse_client_misbehaviour_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let client_id = parse_client_id(&attrs, "client_id")?;
    let client_type = parse_client_type(&attrs, "client_type")?;
    let consensus_height = parse_height(&attrs, "consensus_height")?;

    let attributes = ClientEvents::Attributes {
        client_id,
        client_type,
        consensus_height,
    };

    Ok(IbcEvent::ClientMisbehaviour(
        ClientEvents::ClientMisbehaviour(attributes),
    ))
}

//
// Connection event parsers
//

fn parse_connection_open_init_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let connection_id = parse_optional_connection_id(&attrs, "connection_id");
    let client_id = parse_client_id(&attrs, "client_id")?;
    let counterparty_connection_id =
        parse_optional_connection_id(&attrs, "counterparty_connection_id");
    let counterparty_client_id = parse_client_id(&attrs, "counterparty_client_id")?;

    let attributes = ConnectionEvents::Attributes {
        connection_id,
        client_id,
        counterparty_connection_id,
        counterparty_client_id,
    };

    Ok(IbcEvent::OpenInitConnection(ConnectionEvents::OpenInit(
        attributes,
    )))
}

fn parse_connection_open_try_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let connection_id = parse_optional_connection_id(&attrs, "connection_id");
    let client_id = parse_client_id(&attrs, "client_id")?;
    let counterparty_connection_id =
        parse_optional_connection_id(&attrs, "counterparty_connection_id");
    let counterparty_client_id = parse_client_id(&attrs, "counterparty_client_id")?;

    let attributes = ConnectionEvents::Attributes {
        connection_id,
        client_id,
        counterparty_connection_id,
        counterparty_client_id,
    };

    Ok(IbcEvent::OpenTryConnection(ConnectionEvents::OpenTry(
        attributes,
    )))
}

fn parse_connection_open_ack_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let connection_id = parse_optional_connection_id(&attrs, "connection_id");
    let client_id = parse_client_id(&attrs, "client_id")?;
    let counterparty_connection_id =
        parse_optional_connection_id(&attrs, "counterparty_connection_id");
    let counterparty_client_id = parse_client_id(&attrs, "counterparty_client_id")?;

    let attributes = ConnectionEvents::Attributes {
        connection_id,
        client_id,
        counterparty_connection_id,
        counterparty_client_id,
    };

    Ok(IbcEvent::OpenAckConnection(ConnectionEvents::OpenAck(
        attributes,
    )))
}

fn parse_connection_open_confirm_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let connection_id = parse_optional_connection_id(&attrs, "connection_id");
    let client_id = parse_client_id(&attrs, "client_id")?;
    let counterparty_connection_id =
        parse_optional_connection_id(&attrs, "counterparty_connection_id");
    let counterparty_client_id = parse_client_id(&attrs, "counterparty_client_id")?;

    let attributes = ConnectionEvents::Attributes {
        connection_id,
        client_id,
        counterparty_connection_id,
        counterparty_client_id,
    };

    Ok(IbcEvent::OpenConfirmConnection(
        ConnectionEvents::OpenConfirm(attributes),
    ))
}

//
// Channel event parsers
//

fn parse_channel_open_init_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_optional_channel_id(&attrs, "channel_id");
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::OpenInitChannel(ChannelEvents::OpenInit {
        port_id,
        channel_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

fn parse_channel_open_try_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_optional_channel_id(&attrs, "channel_id");
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::OpenTryChannel(ChannelEvents::OpenTry {
        port_id,
        channel_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

fn parse_channel_open_ack_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_optional_channel_id(&attrs, "channel_id");
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::OpenAckChannel(ChannelEvents::OpenAck {
        port_id,
        channel_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

fn parse_channel_open_confirm_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_optional_channel_id(&attrs, "channel_id");
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::OpenConfirmChannel(ChannelEvents::OpenConfirm {
        port_id,
        channel_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

fn parse_channel_close_init_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_channel_id(&attrs, "channel_id")?;
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::CloseInitChannel(ChannelEvents::CloseInit {
        port_id,
        channel_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

fn parse_channel_close_confirm_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let port_id = parse_port_id(&attrs, "port_id")?;
    let channel_id = parse_optional_channel_id(&attrs, "channel_id");
    let connection_id = parse_connection_id(&attrs, "connection_id")?;
    let counterparty_port_id = parse_port_id(&attrs, "counterparty_port_id")?;
    let counterparty_channel_id = parse_optional_channel_id(&attrs, "counterparty_channel_id");

    Ok(IbcEvent::CloseConfirmChannel(ChannelEvents::CloseConfirm {
        channel_id,
        port_id,
        connection_id,
        counterparty_port_id,
        counterparty_channel_id,
    }))
}

//
// Packet event parsers
//

fn parse_send_packet_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    Ok(IbcEvent::SendPacket(ChannelEvents::SendPacket { packet }))
}

fn parse_recv_packet_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    Ok(IbcEvent::ReceivePacket(ChannelEvents::ReceivePacket {
        packet,
    }))
}

fn parse_write_acknowledgement_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    let ack = parse_bytes(&attrs, "packet_ack")?;
    Ok(IbcEvent::WriteAcknowledgement(
        ChannelEvents::WriteAcknowledgement { packet, ack },
    ))
}

fn parse_acknowledge_packet_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    Ok(IbcEvent::AcknowledgePacket(
        ChannelEvents::AcknowledgePacket { packet },
    ))
}

fn parse_timeout_packet_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    Ok(IbcEvent::TimeoutPacket(ChannelEvents::TimeoutPacket {
        packet,
    }))
}

fn parse_timeout_on_close_packet_event(attrs: HashMap<String, String>) -> Result<IbcEvent, Error> {
    let packet = parse_packet(&attrs)?;
    Ok(IbcEvent::TimeoutOnClosePacket(
        ChannelEvents::TimeoutOnClosePacket { packet },
    ))
}

//
// Helper functions for parsing attribute values
//

fn parse_client_id(attrs: &HashMap<String, String>, key: &str) -> Result<ClientId, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    ClientId::from_str(value)
        .map_err(|e| Error::EventAttribute(format!("Invalid client_id '{}': {}", value, e)))
}

fn parse_client_type(
    attrs: &HashMap<String, String>,
    key: &str,
) -> Result<ibc_relayer_types::core::ics02_client::client_type::ClientType, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    match value.as_str() {
        "cardano" | "08-cardano" => {
            Ok(ibc_relayer_types::core::ics02_client::client_type::ClientType::Cardano)
        }
        "tendermint" | "07-tendermint" => {
            Ok(ibc_relayer_types::core::ics02_client::client_type::ClientType::Tendermint)
        }
        _ => Err(Error::EventAttribute(format!(
            "Unknown client type: {}",
            value
        ))),
    }
}

fn parse_height(attrs: &HashMap<String, String>, key: &str) -> Result<Height, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    // Height format: "revision_number-revision_height" (e.g., "0-100")
    let parts: Vec<&str> = value.split('-').collect();
    if parts.len() != 2 {
        return Err(Error::EventAttribute(format!(
            "Invalid height format '{}', expected 'revision-height'",
            value
        )));
    }

    let revision_number = parts[0].parse::<u64>().map_err(|e| {
        Error::EventAttribute(format!("Invalid revision number '{}': {}", parts[0], e))
    })?;
    let revision_height = parts[1].parse::<u64>().map_err(|e| {
        Error::EventAttribute(format!("Invalid revision height '{}': {}", parts[1], e))
    })?;

    Height::new(revision_number, revision_height)
        .map_err(|e| Error::EventAttribute(format!("Invalid height: {}", e)))
}

fn parse_timeout_height(
    attrs: &HashMap<String, String>,
    key: &str,
) -> Result<TimeoutHeight, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    match Height::from_str(value) {
        Ok(height) => Ok(TimeoutHeight::from(height)),
        Err(e) => {
            let error_message = e.to_string();
            match e.into_detail() {
                HeightErrorDetail::ZeroHeight(_) => Ok(TimeoutHeight::no_timeout()),
                _ => Err(Error::EventAttribute(format!(
                    "Invalid height: {}",
                    error_message
                ))),
            }
        }
    }
}

fn parse_connection_id(attrs: &HashMap<String, String>, key: &str) -> Result<ConnectionId, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    ConnectionId::from_str(value)
        .map_err(|e| Error::EventAttribute(format!("Invalid connection_id '{}': {}", value, e)))
}

fn parse_optional_connection_id(
    attrs: &HashMap<String, String>,
    key: &str,
) -> Option<ConnectionId> {
    attrs.get(key).and_then(|v| ConnectionId::from_str(v).ok())
}

fn parse_port_id(attrs: &HashMap<String, String>, key: &str) -> Result<PortId, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    PortId::from_str(value)
        .map_err(|e| Error::EventAttribute(format!("Invalid port_id '{}': {}", value, e)))
}

fn parse_channel_id(attrs: &HashMap<String, String>, key: &str) -> Result<ChannelId, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    ChannelId::from_str(value)
        .map_err(|e| Error::EventAttribute(format!("Invalid channel_id '{}': {}", value, e)))
}

fn parse_optional_channel_id(attrs: &HashMap<String, String>, key: &str) -> Option<ChannelId> {
    attrs.get(key).and_then(|v| ChannelId::from_str(v).ok())
}

fn parse_u64(attrs: &HashMap<String, String>, key: &str) -> Result<u64, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    value
        .parse::<u64>()
        .map_err(|e| Error::EventAttribute(format!("Invalid u64 '{}': {}", value, e)))
}

fn parse_bytes(attrs: &HashMap<String, String>, key: &str) -> Result<Vec<u8>, Error> {
    let value = attrs
        .get(key)
        .ok_or_else(|| Error::EventAttribute(format!("Missing attribute: {}", key)))?;

    let value_trimmed = value.strip_prefix("0x").unwrap_or(value);
    match hex::decode(value_trimmed) {
        Ok(bytes) => Ok(bytes),
        Err(_) => Ok(value.as_bytes().to_vec()),
    }
}

fn parse_packet(attrs: &HashMap<String, String>) -> Result<Packet, Error> {
    let sequence = parse_u64(attrs, "packet_sequence")?;
    let source_port = parse_port_id(attrs, "packet_src_port")?;
    let source_channel = parse_channel_id(attrs, "packet_src_channel")?;
    let destination_port = parse_port_id(attrs, "packet_dst_port")?;
    let destination_channel = parse_channel_id(attrs, "packet_dst_channel")?;
    let data = parse_bytes(attrs, "packet_data")?;
    let timeout_height = parse_timeout_height(attrs, "packet_timeout_height")?;
    let timeout_timestamp_nanos = parse_u64(attrs, "packet_timeout_timestamp")?;
    let timeout_timestamp = Timestamp::from_nanoseconds(timeout_timestamp_nanos)
        .map_err(|e| Error::EventAttribute(format!("Invalid timestamp: {}", e)))?;

    Ok(Packet {
        sequence: sequence.into(),
        source_port,
        source_channel,
        destination_port,
        destination_channel,
        data,
        timeout_height,
        timeout_timestamp,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc_relayer_types::core::ics02_client::height::Height;
    use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
    use ibc_relayer_types::events::IbcEvent as RelayerIbcEvent;

    fn attrs(kvs: &[(&str, &str)]) -> Vec<EventAttribute> {
        kvs.iter()
            .map(|(k, v)| EventAttribute {
                key: (*k).to_string(),
                value: (*v).to_string(),
            })
            .collect()
    }

    #[test]
    fn parse_timeout_on_close_packet_event_ok() {
        let gateway_event = Event {
            r#type: "timeout_on_close_packet".to_string(),
            attributes: attrs(&[
                ("packet_sequence", "7"),
                ("packet_src_port", "transfer"),
                ("packet_src_channel", "channel-0"),
                ("packet_dst_port", "transfer"),
                ("packet_dst_channel", "channel-1"),
                ("packet_data", "deadbeef"),
                ("packet_timeout_height", "0-10"),
                ("packet_timeout_timestamp", "1000"),
            ]),
        };

        let height = Height::new(0, 1).unwrap();
        let events = parse_events(vec![gateway_event], height).unwrap();

        assert_eq!(events.len(), 1);
        match &events[0] {
            RelayerIbcEvent::TimeoutOnClosePacket(ev) => {
                assert_eq!(ev.packet.sequence, 7.into());
                assert_eq!(ev.packet.source_port.as_str(), "transfer");
                assert_eq!(ev.packet.source_channel.as_str(), "channel-0");
                assert_eq!(ev.packet.destination_port.as_str(), "transfer");
                assert_eq!(ev.packet.destination_channel.as_str(), "channel-1");
                assert_eq!(ev.packet.data, hex::decode("deadbeef").unwrap());
            }
            other => panic!("unexpected event: {other:?}"),
        }
    }

    #[test]
    fn parse_timeout_on_close_packet_event_missing_attr_fails() {
        let gateway_event = Event {
            r#type: "timeout_on_close_packet".to_string(),
            attributes: attrs(&[
                ("packet_sequence", "7"),
                ("packet_src_port", "transfer"),
                ("packet_src_channel", "channel-0"),
                ("packet_dst_port", "transfer"),
                ("packet_dst_channel", "channel-1"),
                // packet_data missing
                ("packet_timeout_height", "0-10"),
                ("packet_timeout_timestamp", "1000"),
            ]),
        };

        let height = Height::new(0, 1).unwrap();
        let err = parse_events(vec![gateway_event], height).unwrap_err();

        match err {
            Error::EventAttribute(msg) => assert!(msg.contains("Missing attribute: packet_data")),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn parse_timeout_on_close_packet_event_raw_json_data_ok() {
        let payload = r#"{"amount":"1000000","denom":"stake","receiver":"abc","sender":"def"}"#;
        let gateway_event = Event {
            r#type: "timeout_on_close_packet".to_string(),
            attributes: attrs(&[
                ("packet_sequence", "7"),
                ("packet_src_port", "transfer"),
                ("packet_src_channel", "channel-0"),
                ("packet_dst_port", "transfer"),
                ("packet_dst_channel", "channel-1"),
                ("packet_data", payload),
                ("packet_timeout_height", "0-10"),
                ("packet_timeout_timestamp", "1000"),
            ]),
        };

        let height = Height::new(0, 1).unwrap();
        let events = parse_events(vec![gateway_event], height).unwrap();

        assert_eq!(events.len(), 1);
        match &events[0] {
            RelayerIbcEvent::TimeoutOnClosePacket(ev) => {
                assert_eq!(ev.packet.data, payload.as_bytes().to_vec());
            }
            other => panic!("unexpected event: {other:?}"),
        }
    }

    #[test]
    fn parse_send_packet_event_zero_timeout_height_maps_to_no_timeout() {
        let gateway_event = Event {
            r#type: "send_packet".to_string(),
            attributes: attrs(&[
                ("packet_sequence", "9"),
                ("packet_src_port", "transfer"),
                ("packet_src_channel", "channel-0"),
                ("packet_dst_port", "transfer"),
                ("packet_dst_channel", "channel-1"),
                ("packet_data", "deadbeef"),
                ("packet_timeout_height", "0-0"),
                ("packet_timeout_timestamp", "1000"),
            ]),
        };

        let height = Height::new(0, 1).unwrap();
        let events = parse_events(vec![gateway_event], height).unwrap();

        assert_eq!(events.len(), 1);
        match &events[0] {
            RelayerIbcEvent::SendPacket(ev) => {
                assert_eq!(ev.packet.timeout_height, TimeoutHeight::no_timeout());
            }
            other => panic!("unexpected event: {other:?}"),
        }
    }
}
