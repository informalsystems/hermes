use alloc::sync::Arc;

use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use tendermint::abci::Event as AbciEvent;

use ibc_relayer_types::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc_relayer_types::events::IbcEventType;

pub fn try_extract_send_packet_event(event: &Arc<AbciEvent>) -> Option<SendPacket> {
    let event_type = event.kind.parse().ok()?;

    if let IbcEventType::SendPacket = event_type {
        let (packet, _) = extract_packet_and_write_ack_from_tx(event).ok()?;

        let send_packet_event = SendPacket { packet };

        Some(send_packet_event)
    } else {
        None
    }
}

pub fn try_extract_write_acknowledgement_event(
    event: &Arc<AbciEvent>,
) -> Option<WriteAcknowledgement> {
    if let IbcEventType::WriteAck = event.kind.parse().ok()? {
        let (packet, write_ack) = extract_packet_and_write_ack_from_tx(event).ok()?;

        let ack = WriteAcknowledgement {
            packet,
            ack: write_ack,
        };

        Some(ack)
    } else {
        None
    }
}
