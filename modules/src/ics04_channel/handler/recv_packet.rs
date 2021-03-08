use std::cmp::Ordering;

use crate::{handler::{HandlerOutput, HandlerResult}, ics24_host::identifier::{ChannelId, PortId}};
use crate::{events::IbcEvent, ics04_channel::events::ReceivePacket};


use super::verify::verify_packet_proofs;
use crate::ics02_client::state::ClientState;
use crate::ics03_connection::connection::State as ConnectionState;

use crate::ics04_channel::channel::{Counterparty,Order, State};
use crate::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use crate::ics04_channel::packet::{PacketResult, Sequence};
use crate::ics04_channel::{context::ChannelReader, error::Error, error::Kind};
#[derive(Clone, Debug)]
pub struct RecvPacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub seq: Sequence,
    pub seq_number: Sequence,
    pub receipt: Option<String>
}


pub fn process(ctx: &dyn ChannelReader, msg: MsgRecvPacket) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    let packet = msg.packet.clone();
    let dest_channel_end = ctx
        .channel_end(&(
            packet.destination_port.clone(),
            packet.destination_channel.clone(),
        ))
        .ok_or_else(|| {
            Kind::ChannelNotFound(
                packet.destination_port.clone(),
                packet.destination_channel.clone(),
            )
        })?;

    if !dest_channel_end.state_matches(&State::Open) {
        return Err(
            Kind::InvalidChannelState(packet.source_channel, dest_channel_end.state).into(),
        );
    }
    let _channel_cap = ctx.authenticated_capability(&packet.destination_port)?;

    let counterparty = Counterparty::new(
        packet.source_port.clone(),
        Some(packet.source_channel.clone()),
    );

    if !dest_channel_end.counterparty_matches(&counterparty) {
        return Err(Kind::InvalidPacketCounterparty(
            packet.source_port.clone(),
            packet.source_channel,
        )
        .into());
    }

    let connection_end = ctx
        .connection_end(&dest_channel_end.connection_hops()[0])
        .ok_or_else(|| Kind::MissingConnection(dest_channel_end.connection_hops()[0].clone()))?;

    if !connection_end.state_matches(&ConnectionState::Open) {
        return Err(Kind::ConnectionNotOpen(dest_channel_end.connection_hops()[0].clone()).into());
    }

    let client_id = connection_end.client_id().clone();

    let client_state = ctx
        .client_state(&client_id)
        .ok_or_else(|| Kind::MissingClientState(client_id.clone()))?;
    // check if packet height timeouted on the receiving chain

    // prevent accidental sends with clients that cannot be updated
    if client_state.is_frozen() {
        return Err(Kind::FrozenClient(connection_end.client_id().clone()).into());
    }

    let latest_height = client_state.latest_height();
    let packet_height = packet.timeout_height;

    if !packet.timeout_height.is_zero() && packet_height.cmp(&latest_height).eq(&Ordering::Less) {
        return Err(Kind::LowPacketHeight(latest_height, packet.timeout_height).into());
    }

    //check if packet timestamp timeouted on the receiving chain
    let consensus_state = ctx
        .client_consensus_state(&client_id, latest_height)
        .ok_or_else(|| Kind::MissingClientConsensusState(client_id.clone(), latest_height))?;

    let latest_timestamp = consensus_state.timestamp()
        .map_err(Kind::ErrorInvalidConsensusState)?;
    

    let packet_timestamp = packet.timeout_timestamp;
    if !packet.timeout_timestamp == 0 && packet_timestamp.cmp(&latest_timestamp).eq(&Ordering::Less)
    {
        return Err(Kind::LowPacketTimestamp.into());
    }

    verify_packet_proofs(ctx, &packet, client_id, &msg.proofs.clone())?;

    //map_or_else(|| Kind::PacketVerificationFailed(packet.sequence.clone()))?;

    output.log("success: packet send ");
    let result;

    if dest_channel_end.order_matches(&Order::Ordered) {
        let next_seq_recv = ctx
            .get_next_sequence_recv(&(packet.source_port.clone(), packet.source_channel.clone()))
            .ok_or(Kind::MissingNextRecvSeq)?;

        if !packet.sequence.eq(&next_seq_recv) {
            return Err(Kind::InvalidPacketSequence(packet.sequence, next_seq_recv).into());
        }
        
        result = PacketResult::Recv(RecvPacketResult {
            port_id: packet.source_port.clone(),
            channel_id: packet.source_channel.clone(),
            seq: packet.sequence.clone(),
            seq_number: next_seq_recv.increment(),
            receipt: None,
        });
    } else {
        let packet_rec = ctx.get_packet_receipt(&(
            packet.source_port.clone(),
            packet.source_channel.clone(),
            packet.sequence.clone(),
        ));

        match packet_rec {
            Some(_r) => {
                return Err(Kind::PacketReceived(<u64 as From<Sequence>>::from(
                    packet.sequence.clone(),
                ))
                .into())
            }
            None => {
                result = PacketResult::Recv(RecvPacketResult {
                    port_id: packet.source_port.clone(),
                    channel_id: packet.source_channel.clone(),
                    seq: packet.sequence.clone(),
                    seq_number: 1.into(),
                    receipt: Some("1".to_string()),
                });
            }
        }
    }

    output.emit(IbcEvent::ReceivePacket(ReceivePacket {
        height: packet_height,
        packet,
    }));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {

    use std::convert::TryFrom;

    use crate::ics02_client::height::Height;
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::version::get_compatible_versions;
    use crate::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
    use crate::ics04_channel::msgs::recv_packet::test_util::get_dummy_raw_msg_recv_packet;
    use crate::ics04_channel::msgs::recv_packet::MsgRecvPacket;
    use crate::ics04_channel::handler::recv_packet::process;
    use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::mock::context::MockContext;
    use crate::{
        events::IbcEvent,
        ics04_channel::packet::{Packet, Sequence},
    };
    use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgRecvPacket;

    #[test]
    fn recv_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            packet: Packet,
            want_pass: bool,
        }

        let context = MockContext::default();

        let height = Height::default().revision_height + 1;

        let h = Height::new(0, Height::default().revision_height + 1);

        let raw_msg = get_dummy_raw_msg_recv_packet(height);
        
        let msg = <MsgRecvPacket as TryFrom<RawMsgRecvPacket>>::try_from(raw_msg).unwrap();
        
        //let msg:MsgRecvPacket = raw_msg.into();

        //map_err(|e| Kind::InvalidPacket.context(e).into()).into_ok();
        //unwrap_or_else(return Error::Kind::InvalidPacket.context(e).into());
        //map_err(|e| Kind::InvalidPacket.context(e).into());
        let packet = msg.packet.clone();

        let packet_untimed = Packet {
            sequence: <Sequence as From<u64>>::from(1),
            source_port: PortId::default(),
            source_channel: ChannelId::default(),
            destination_port: PortId::default(),
            destination_channel: ChannelId::default(),
            data: vec![],
            timeout_height: Height::default(),
            timeout_timestamp: 0,
        };


        let dest_channel_end = ChannelEnd::new(
            State::Open,
            Order::default(),
            Counterparty::new(
                packet.source_port.clone(),
                Some(packet.source_channel.clone()),
            ),
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
                ctx: context.clone().with_channel(
                    PortId::default(),
                    ChannelId::default(),
                    dest_channel_end.clone(),
                ),
                packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), h)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_port_capability(packet.destination_port.clone())
                    .with_channel(
                        packet.destination_port.clone(),
                        packet.destination_channel.clone(),
                        dest_channel_end.clone(),
                    )
                    .with_send_sequence(
                        packet.destination_port.clone(),
                        packet.destination_channel.clone(),
                        1.into(),
                    ),
                packet,
                want_pass: true,
            },
            Test {
                name: "Zero timeout".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), Height::default())
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_port_capability(PortId::default())
                    .with_channel(PortId::default(), ChannelId::default(), dest_channel_end)
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_untimed,
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = process(&test.ctx, msg.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "recv_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // TODO: The object in the output is a PacketResult what can we check on it?

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::ReceivePacket(_)));
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
