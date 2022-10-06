use crate::core::ics04_channel::channel::Counterparty;
use crate::core::ics04_channel::channel::State;
use crate::core::ics04_channel::commitment::PacketCommitment;
use crate::core::ics04_channel::events::SendPacket;
use crate::core::ics04_channel::packet::{PacketResult, Sequence};
use crate::core::ics04_channel::{context::ChannelReader, error::Error, packet::Packet};
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;
use crate::timestamp::Expiry;

#[derive(Clone, Debug)]
pub struct SendPacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub seq: Sequence,
    pub seq_number: Sequence,
    pub commitment: PacketCommitment,
}

pub fn send_packet(ctx: &dyn ChannelReader, packet: Packet) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    let source_channel_end = ctx.channel_end(&packet.source_port, &packet.source_channel)?;

    if source_channel_end.state_matches(&State::Closed) {
        return Err(Error::channel_closed(packet.source_channel));
    }

    let counterparty = Counterparty::new(
        packet.destination_port.clone(),
        Some(packet.destination_channel.clone()),
    );

    if !source_channel_end.counterparty_matches(&counterparty) {
        return Err(Error::invalid_packet_counterparty(
            packet.destination_port.clone(),
            packet.destination_channel,
        ));
    }

    let connection_end = ctx.connection_end(&source_channel_end.connection_hops()[0])?;

    let client_id = connection_end.client_id().clone();

    let client_state = ctx.client_state(&client_id)?;

    // prevent accidental sends with clients that cannot be updated
    if client_state.is_frozen() {
        return Err(Error::frozen_client(connection_end.client_id().clone()));
    }

    let latest_height = client_state.latest_height();

    if packet.timeout_height.has_expired(latest_height) {
        return Err(Error::low_packet_height(
            latest_height,
            packet.timeout_height,
        ));
    }

    let consensus_state = ctx.client_consensus_state(&client_id, latest_height)?;
    let latest_timestamp = consensus_state.timestamp();
    let packet_timestamp = packet.timeout_timestamp;
    if let Expiry::Expired = latest_timestamp.check_expiry(&packet_timestamp) {
        return Err(Error::low_packet_timestamp());
    }

    let next_seq_send = ctx.get_next_sequence_send(&packet.source_port, &packet.source_channel)?;

    if packet.sequence != next_seq_send {
        return Err(Error::invalid_packet_sequence(
            packet.sequence,
            next_seq_send,
        ));
    }

    output.log("success: packet send ");

    let result = PacketResult::Send(SendPacketResult {
        port_id: packet.source_port.clone(),
        channel_id: packet.source_channel.clone(),
        seq: packet.sequence,
        seq_number: next_seq_send.increment(),
        commitment: ctx.packet_commitment(
            packet.data.clone(),
            packet.timeout_height,
            packet.timeout_timestamp,
        ),
    });

    output.emit(IbcEvent::SendPacket(SendPacket { packet }));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use core::ops::Add;
    use core::time::Duration;

    use test_log::test;

    use crate::core::ics02_client::height::Height;
    use crate::core::ics03_connection::connection::ConnectionEnd;
    use crate::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::core::ics03_connection::connection::State as ConnectionState;
    use crate::core::ics03_connection::version::get_compatible_versions;
    use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
    use crate::core::ics04_channel::handler::send_packet::send_packet;
    use crate::core::ics04_channel::packet::test_utils::get_dummy_raw_packet;
    use crate::core::ics04_channel::packet::Packet;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::prelude::*;
    use crate::timestamp::Timestamp;
    use crate::timestamp::ZERO_DURATION;

    #[test]
    fn send_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            packet: Packet,
            want_pass: bool,
        }

        let context = MockContext::default();

        let channel_end = ChannelEnd::new(
            State::TryOpen,
            Order::default(),
            Counterparty::new(PortId::default(), Some(ChannelId::default())),
            vec![ConnectionId::default()],
            Version::ics20(),
        );

        let connection_end = ConnectionEnd::new(
            ConnectionState::Open,
            ClientId::default(),
            ConnectionCounterparty::new(
                ClientId::default(),
                Some(ConnectionId::default()),
                Default::default(),
            ),
            get_compatible_versions(),
            ZERO_DURATION,
        );

        let timestamp_future = Timestamp::now().add(Duration::from_secs(10)).unwrap();
        let timestamp_ns_past = 1;

        let timeout_height_future = 10;

        let mut packet: Packet =
            get_dummy_raw_packet(timeout_height_future, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();
        packet.sequence = 1.into();
        packet.data = vec![0];

        let mut packet_with_timestamp_old: Packet =
            get_dummy_raw_packet(timeout_height_future, timestamp_ns_past)
                .try_into()
                .unwrap();
        packet_with_timestamp_old.sequence = 1.into();
        packet_with_timestamp_old.data = vec![0];

        let client_raw_height = 5;
        let packet_timeout_equal_client_height: Packet =
            get_dummy_raw_packet(client_raw_height, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();
        let packet_timeout_one_before_client_height: Packet =
            get_dummy_raw_packet(client_raw_height - 1, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();

        let client_height = Height::new(0, client_raw_height).unwrap();

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no channel exists in the context".to_string(),
                ctx: context.clone(),
                packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet,
                want_pass: true,
            },
            Test {
                name: "Packet timeout height same as destination chain height".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_timeout_equal_client_height,
                want_pass: true,
            },
            Test {
                name: "Packet timeout height one more than destination chain height".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_timeout_one_before_client_height,
                want_pass: false,
            },
            Test {
                name: "Packet timeout due to timestamp".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_channel(PortId::default(), ChannelId::default(), channel_end)
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_with_timestamp_old,
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = send_packet(&test.ctx, test.packet.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert!(
                        test.want_pass,
                        "send_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone()
                    );

                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // TODO: The object in the output is a PacketResult what can we check on it?
                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::SendPacket(_)));
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "send_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
