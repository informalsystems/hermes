use core::time::Duration;

use ibc_relayer_types::{
    core::{
        ics03_connection::connection::{
            ConnectionEnd, Counterparty as ConnectionCounterparty, IdentifiedConnectionEnd,
            State as ConnectionState,
        },
        ics04_channel::{
            channel::{
                ChannelEnd, Counterparty as ChannelCounterparty, IdentifiedChannelEnd, Order,
                State as ChannelState,
            },
            version::Version as ChannelVersion,
        },
        ics23_commitment::commitment::CommitmentPrefix,
    },
    events::IbcEvent,
};

pub fn is_connection_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::OpenInitConnection(_)
            | &IbcEvent::OpenTryConnection(_)
            | &IbcEvent::OpenAckConnection(_)
            | &IbcEvent::OpenConfirmConnection(_)
    )
}

macro_rules! event_to_connection {
    ($ev:expr, $state:expr) => {
        IdentifiedConnectionEnd {
            connection_id: $ev.connection_id().cloned().unwrap(),
            connection_end: ConnectionEnd::new(
                $state, // missing from connection events
                $ev.attributes().client_id.clone(),
                ConnectionCounterparty::new(
                    $ev.attributes().counterparty_client_id.clone(),
                    $ev.attributes().counterparty_connection_id.clone(),
                    CommitmentPrefix::default(), // missing from connection events
                ),
                vec![],              // missing from connection events
                Duration::default(), // missing from connection events
            ),
        }
    };
}

pub fn connection_from_event(event: &IbcEvent) -> Option<IdentifiedConnectionEnd> {
    match event {
        IbcEvent::OpenInitConnection(ev) => Some(event_to_connection!(ev, ConnectionState::Init)),
        IbcEvent::OpenTryConnection(ev) => Some(event_to_connection!(ev, ConnectionState::TryOpen)),
        IbcEvent::OpenAckConnection(ev) => Some(event_to_connection!(ev, ConnectionState::Open)),
        IbcEvent::OpenConfirmConnection(ev) => {
            Some(event_to_connection!(ev, ConnectionState::Open))
        }
        _ => None,
    }
}

pub fn is_channel_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::OpenInitChannel(_)
            | &IbcEvent::OpenTryChannel(_)
            | &IbcEvent::OpenAckChannel(_)
            | &IbcEvent::OpenConfirmChannel(_)
    )
}

macro_rules! event_to_channel {
    ($ev:expr, $state:expr) => {
        IdentifiedChannelEnd::new(
            $ev.port_id.clone(),
            $ev.channel_id.clone().unwrap(),
            ChannelEnd::new(
                $state,      // missing from channel events
                Order::None, // missing from channel events
                ChannelCounterparty::new(
                    $ev.counterparty_port_id.clone(),
                    $ev.counterparty_channel_id.clone(),
                ),
                vec![$ev.connection_id.clone()],
                ChannelVersion::empty(), // missing from channel events
            ),
        )
    };
}

pub fn channel_from_event(event: &IbcEvent) -> Option<IdentifiedChannelEnd> {
    match event {
        IbcEvent::OpenInitChannel(ev) => Some(event_to_channel!(ev, ChannelState::Init)),
        IbcEvent::OpenTryChannel(ev) => Some(event_to_channel!(ev, ChannelState::TryOpen)),
        IbcEvent::OpenAckChannel(ev) => Some(event_to_channel!(ev, ChannelState::Open)),
        IbcEvent::OpenConfirmChannel(ev) => Some(event_to_channel!(ev, ChannelState::Open)),
        _ => None,
    }
}

pub fn is_packet_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::SendPacket(_)
            | &IbcEvent::WriteAcknowledgement(_)
            | &IbcEvent::AcknowledgePacket(_)
    )
}

pub fn is_client_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::CreateClient(_) | &IbcEvent::UpdateClient(_)
    )
}
