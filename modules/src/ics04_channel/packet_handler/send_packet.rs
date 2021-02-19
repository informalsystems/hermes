use std::{cmp::Ordering, convert::TryFrom, ops::Add, time::Duration};
use tendermint::block::Height;

use crate::{events::IBCEvent, ics02_client::client_def::AnyTime};
use crate::handler::{HandlerOutput, HandlerResult};

use crate::ics02_client::state::ClientState;
use crate::ics04_channel::channel::Counterparty;
use crate::ics04_channel::channel::State;
use crate::ics04_channel::events::SendPacket;
use crate::ics04_channel::packet::Sequence;
use crate::ics04_channel::{context::ChannelReader, error::Error, error::Kind, packet::Packet};
//use sha2::{Sha256, Digest};


use super::PacketResult;

pub fn send_packet(ctx: &dyn ChannelReader, packet: Packet) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    // TODO: check if there is a validate basic. Maybe it should be in the message.

    let source_channel_end = ctx
        .channel_end(&(packet.source_port.clone(), packet.source_channel.clone()))
        .ok_or_else(|| Kind::ChannelNotFound.context(packet.source_channel.clone().to_string()))?;

    if source_channel_end.state_matches(&State::Closed) {
        return Err(Kind::ChannelClosed(packet.source_channel).into());
    }

    // TODO: Capability Checked in ICS20 as well. Check Difs.
    let _channel_cap = ctx.authenticated_capability(&packet.source_port)?;

    let channel_id = match source_channel_end.counterparty().channel_id() {
        Some(c) => Some(c.clone()),
        None => None,
    };

    let counterparty = Counterparty::new(
        source_channel_end.counterparty().port_id().clone(),
        channel_id,
    );

    if !source_channel_end.counterparty_matches(&counterparty) {
        return Err(Kind::InvalidPacketCounterparty(
            packet.source_port.clone(),
            packet.source_channel,
        )
        .into());
    }

    let connection_end = ctx
        .connection_end(&source_channel_end.connection_hops()[0])
        .ok_or_else(|| Kind::MissingConnection(source_channel_end.connection_hops()[0].clone()))?;

    let client_state = ctx
        .channel_client_state(&(packet.source_port.clone(), packet.source_channel.clone()))
        .ok_or_else(|| Kind::MissingClientState)?;

    // prevent accidental sends with clients that cannot be updated
    if client_state.is_frozen() {
        return Err(Kind::FrozenClient(connection_end.client_id().clone()).into());
    }

    // check if packet height timeouted on the receiving chain
    // The height should be computed w.r.t. the current height, w.r,t, only revision_height or also revision_number ?
    // In Go it's not in msg and spec it says it should.

    let latest_height = client_state.latest_height();
    //let packet_height = packet.timeout_height;
    let packet_height = ctx
        .channel_host_current_height()
        .add(packet.timeout_height.revision_height);
    if !packet.timeout_height.is_zero() && packet_height.cmp(&latest_height).eq(&Ordering::Less) {
        return Err(Kind::LowPacketHeight(latest_height, packet.timeout_height).into());
    }

    //check if packet timestamp timeouted on the receiving chain
    let consensus_state = ctx
        .channel_client_consensus_state(
            &(packet.source_port.clone(), packet.source_channel.clone()),
            latest_height,
        )
        .ok_or_else(|| Kind::MissingClientConsensusState)?;

    let latest_timestamp = consensus_state.latest_timestamp();

    let host_consensus_state = ctx
        .channel_host_consensus_state()
        .ok_or_else(|| Kind::MissingHostConsensusState)?;
    let mut packet_timestamp = host_consensus_state.latest_timestamp();

    packet_timestamp = <AnyTime as Add<Duration>>::add(
        packet_timestamp,
        Duration::from_nanos(packet.timeout_timestamp),
    );

    if !packet.timeout_timestamp == 0 && packet_timestamp.cmp(&latest_timestamp).eq(&Ordering::Less)
    {
        return Err(Kind::LowPacketTimestamp.into());
    }

    // check sequence number
    let next_seq_send = ctx
        .get_next_sequence_send(&(packet.source_port.clone(), packet.source_channel.clone()))
        .ok_or_else(|| Kind::MissingNextSendSeq)?;

    if !packet.sequence.eq(&Sequence::from(*next_seq_send)) {
        return Err(
            Kind::InvalidPacketSequence(packet.sequence, Sequence::from(*next_seq_send)).into(),
        );
    }

    //let mut sha =  Sha256::default();
    //let res = sha2::Sha256::digest(packet.clone().timeout_timestamp);
    //sha.update(packet.clone().timeout_timestamp);
    // //+packet.clone().timeout_height+packet.clone().data
    //let commitment = sha2::Sha256::digest(packet.clone().timeout_timestamp);
    //commitment.
    //sha2.result_bytes();

    let commitment = packet.clone().timeout_timestamp;
    // let commitment = CommitmentPrefix::get_prefix(
    //     packet.clone().data,
    //     packet.clone().timeout_height,
    //     packet.clone().timeout_timestamp,
    // );

    output.log("success: packet send ");

    let result = PacketResult {
        port_id:packet.source_port.clone(),
        channel_id:packet.source_channel.clone(),
        send_seq_number: Sequence::from(*next_seq_send+1),
        commitment
    };

    let height = <Height as TryFrom<u64>>::try_from(packet_height.revision_height).unwrap();

    output.emit(IBCEvent::SendPacketChannel(SendPacket { height, packet }));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {

    use crate::ics02_client::height::Height;
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::version::get_compatible_versions;
    use crate::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
    use crate::ics04_channel::packet_handler::send_packet::send_packet;
    use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::mock::context::MockContext;
    use crate::{
        events::IBCEvent,
        ics04_channel::packet::{Packet, Sequence},
    };

    #[test]
    fn send_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            packet: Packet,
            want_pass: bool,
        }

        let context = MockContext::default();

        let packet = Packet {
            sequence: <Sequence as From<u64>>::from(1),
            source_port: PortId::default(),
            source_channel: ChannelId::default(),
            destination_port: PortId::default(),
            destination_channel: ChannelId::default(),
            data: vec![],
            timeout_height: Height::default(),
            timeout_timestamp: 0,
        };

        let packet_timed = Packet {
            sequence: <Sequence as From<u64>>::from(1),
            source_port: PortId::default(),
            source_channel: ChannelId::default(),
            destination_port: PortId::default(),
            destination_channel: ChannelId::default(),
            data: vec![],
            timeout_height: Height::default(),
            timeout_timestamp: 6,
        };

        let channel_end = ChannelEnd::new(
            State::TryOpen,
            Order::default(),
            Counterparty::new(PortId::default(), Some(ChannelId::default())),
            vec![ConnectionId::default()],
            "ics20".to_string(),
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
            0,
        );

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no channel exists in the context".to_string(),
                ctx: context.clone(),
                packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the port does not have a capability associated"
                    .to_string(),
                ctx: context.clone().with_channel_init(
                    PortId::default(),
                    ChannelId::default(),
                    channel_end.clone(),
                ),
                packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context.clone()
                    .with_client(&ClientId::default(), Height::default())
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_port_capability(PortId::default())
                    .with_channel_init(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1),
                packet: packet,
                want_pass: true,
            },
            Test {
                name: "Good parameters with time".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), Height::default())
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_port_capability(PortId::default())
                    .with_channel_init(PortId::default(), ChannelId::default(), channel_end)
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1),
                packet: packet_timed,
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = send_packet(&test.ctx, test.packet.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "send_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // TODO: The object in the output is a PacketResult what can we check on it?
                   
                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IBCEvent::SendPacketChannel(_)));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
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
