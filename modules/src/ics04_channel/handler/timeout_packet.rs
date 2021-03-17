use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics04_channel::channel::State;
use crate::ics04_channel::channel::{Counterparty, Order};
use crate::ics04_channel::events::TimeoutPacket;
use crate::ics04_channel::handler::verify::{verify_packet_receipt_absence,verify_next_sequence_recv};
use crate::ics04_channel::msgs::timeout::MsgTimeout;
use crate::ics04_channel::packet::{PacketResult, Sequence};
use crate::ics04_channel::{context::ChannelReader, error::Error, error::Kind};
use crate::ics24_host::identifier::{ChannelId, PortId};

#[derive(Clone, Debug)]
pub struct TimeoutPacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub seq: Sequence,
}

pub fn process(
    ctx: &dyn ChannelReader,
    msg: MsgTimeout,
) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    let packet = &msg.packet;

    let source_channel_end = ctx
        .channel_end(&(packet.source_port.clone(), packet.source_channel.clone()))
        .ok_or_else(|| {
            Kind::ChannelNotFound(packet.source_port.clone(), packet.source_channel.clone())
                .context(packet.source_channel.to_string())
        })?;

    if !source_channel_end.state_matches(&State::Open) {
        return Err(Kind::ChannelClosed(packet.source_channel.clone()).into());
    }

    let _channel_cap = ctx.authenticated_capability(&packet.source_port)?;
    

    let counterparty = Counterparty::new(
        packet.destination_port.clone(),
        Some(packet.destination_channel.clone()),
    );

    if !source_channel_end.counterparty_matches(&counterparty) {
        return Err(Kind::InvalidPacketCounterparty(
            packet.destination_port.clone(),
            packet.destination_channel.clone(),
        )
        .into());
    }

    let connection_end = ctx
        .connection_end(&source_channel_end.connection_hops()[0])
        .ok_or_else(|| Kind::MissingConnection(source_channel_end.connection_hops()[0].clone()))?;

    let client_id = connection_end.client_id().clone();


    // check that timeout height or timeout timestamp has passed on the other end
    let proof_height = msg.proofs.height().clone();
    let packet_height = packet.timeout_height;

    if (!packet.timeout_height.is_zero()) && packet_height > proof_height{
        return Err(Kind::PacketTOHeightNotReached(packet.timeout_height,proof_height).into());
    }
    
    let consensus_state = ctx
        .client_consensus_state(&client_id, proof_height)
        .ok_or_else(|| Kind::MissingClientConsensusState(client_id.clone(), proof_height))?;

    let proof_timestamp = consensus_state
        .timestamp()
        .map_err(Kind::ErrorInvalidConsensusState)?;

    let packet_timestamp = packet.timeout_timestamp;
    if packet.timeout_timestamp != 0 && packet_timestamp > proof_timestamp {
        return Err(Kind::PacketTOTimestampNotReached(packet_timestamp,proof_timestamp).into());
    }

    //verify packet commitment
    let packet_commitment = ctx
        .get_packet_commitment(&(
            packet.source_port.clone(),
            packet.source_channel.clone(),
            packet.sequence,
        ))
        .ok_or(Kind::PacketCommitmentNotFound(packet.sequence))?;

    let input = format!(
        "{:?},{:?},{:?}",
        packet.timeout_timestamp, packet.timeout_height, packet.data,
    );

    if packet_commitment != ChannelReader::hash(ctx, input) {
        return Err(Kind::IncorrectPacketCommitment(packet.sequence).into());
    }

    if source_channel_end.order_matches(&Order::Ordered) {
        if packet.sequence != msg.next_sequence_recv {
            return Err(Kind::InvalidPacketSequence(packet.sequence, msg.next_sequence_recv).into());
        }
        verify_next_sequence_recv(ctx, client_id, packet.clone(),msg.next_sequence_recv, msg.proofs.clone())?;

    } else {
        verify_packet_receipt_absence(ctx, client_id, packet.clone(),msg.proofs.clone())?;
    };
    
    output.log("success: packet timeout ");

    let result = PacketResult::Timeout(TimeoutPacketResult {
        port_id: packet.source_port.clone(),
        channel_id: packet.source_channel.clone(),
        seq: packet.sequence,
    });

    output.emit(IbcEvent::TimeoutPacket(TimeoutPacket {
        height: Default::default(),
        packet: packet.clone(),
    }));

    Ok(output.with_result(result))
}

// #[cfg(test)]
// mod tests {

//     use crate::events::IbcEvent;
//     use crate::ics02_client::height::Height;
//     use crate::ics03_connection::connection::ConnectionEnd;
//     use crate::ics03_connection::connection::Counterparty as ConnectionCounterparty;
//     use crate::ics03_connection::connection::State as ConnectionState;
//     use crate::ics03_connection::version::get_compatible_versions;
//     use crate::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
//     use crate::ics04_channel::context::ChannelReader;
//     use crate::ics04_channel::handler::acknowledgement::process;
//     use crate::ics04_channel::msgs::acknowledgement::test_util::get_dummy_raw_msg_acknowledgement;
//     use crate::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
//     use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
//     use crate::mock::context::MockContext;

//     use std::convert::TryFrom;

//     #[test]
//     fn ack_packet_processing() {
//         struct Test {
//             name: String,
//             ctx: MockContext,
//             msg: MsgAcknowledgement,
//             want_pass: bool,
//         }

//         let context = MockContext::default();

//         let height = Height::default().revision_height + 2;

//         let client_height = Height::new(0, Height::default().revision_height + 2);

//         let msg = MsgAcknowledgement::try_from(get_dummy_raw_msg_acknowledgement(height)).unwrap();
//         let packet = msg.packet.clone();

//         let input = format!(
//             "{:?},{:?},{:?}",
//             packet.timeout_timestamp,
//             packet.timeout_height.clone(),
//             packet.data.clone()
//         );
//         let data = ChannelReader::hash(&context, input);

//         let source_channel_end = ChannelEnd::new(
//             State::Open,
//             Order::default(),
//             Counterparty::new(
//                 packet.destination_port.clone(),
//                 Some(packet.destination_channel.clone()),
//             ),
//             vec![ConnectionId::default()],
//             "ics20".to_string(),
//         );

//         let connection_end = ConnectionEnd::new(
//             ConnectionState::Open,
//             ClientId::default(),
//             ConnectionCounterparty::new(
//                 ClientId::default(),
//                 Some(ConnectionId::default()),
//                 Default::default(),
//             ),
//             get_compatible_versions(),
//             0,
//         );

//         let tests: Vec<Test> = vec![
//             Test {
//                 name: "Processing fails because no channel exists in the context".to_string(),
//                 ctx: context.clone(),
//                 msg: msg.clone(),
//                 want_pass: false,
//             },
//             Test {
//                 name: "Processing fails because the port does not have a capability associated"
//                     .to_string(),
//                 ctx: context.clone().with_channel(
//                     PortId::default(),
//                     ChannelId::default(),
//                     source_channel_end.clone(),
//                 ),
//                 msg: msg.clone(),
//                 want_pass: false,
//             },
//             Test {
//                 name: "Good parameters".to_string(),
//                 ctx: context
//                     .with_client(&ClientId::default(), client_height)
//                     .with_connection(ConnectionId::default(), connection_end)
//                     .with_port_capability(packet.destination_port.clone())
//                     .with_channel(
//                         packet.source_port.clone(),
//                         packet.source_channel.clone(),
//                         source_channel_end,
//                     )
//                     .with_packet_commitment(
//                         packet.source_port,
//                         packet.source_channel,
//                         packet.sequence,
//                         data,
//                     ) //with_ack_sequence required for ordered channels
//                     .with_ack_sequence(
//                         packet.destination_port,
//                         packet.destination_channel,
//                         1.into(),
//                     ),
//                 msg,
//                 want_pass: true,
//             },
//         ]
//         .into_iter()
//         .collect();

//         for test in tests {
//             let res = process(&test.ctx, test.msg.clone());
//             // Additionally check the events and the output objects in the result.
//             match res {
//                 Ok(proto_output) => {
//                     assert_eq!(
//                         test.want_pass,
//                         true,
//                         "ack_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
//                         test.name,
//                         test.msg.clone(),
//                         test.ctx.clone()
//                     );
//                     assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.
//                     for e in proto_output.events.iter() {
//                         assert!(matches!(e, &IbcEvent::AcknowledgePacket(_)));
//                     }
//                 }
//                 Err(e) => {
//                     assert_eq!(
//                         test.want_pass,
//                         false,
//                         "recv_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
//                         test.name,
//                         test.msg.clone(),
//                         test.ctx.clone(),
//                         e,
//                     );
//                 }
//             }
//         }
//     }
// }
