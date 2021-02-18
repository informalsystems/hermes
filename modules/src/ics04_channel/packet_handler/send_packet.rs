// use std::{cmp::Ordering, convert::TryFrom, ops::Add, time::Duration};

// //use ics23::Hash;
// use tendermint::{Time, block::Height};

use std::{cmp::Ordering, convert::TryFrom};

//use ics23::Hash;
use tendermint::block::Height;

use crate::events::IBCEvent;
use crate::handler::{HandlerOutput, HandlerResult};

use crate::ics02_client::state::ClientState;
use crate::ics04_channel::channel::Counterparty;
use crate::ics04_channel::channel::State;
use crate::ics04_channel::events::SendPacket;
use crate::ics04_channel::packet::Sequence;
use crate::ics04_channel::{context::ChannelReader, error::Error, error::Kind, packet::Packet};
//use crate::ics05_port::capabilities::Capability;
//use crate::Height;

use super::PacketResult;

pub fn send_packet(ctx: &dyn ChannelReader, packet: Packet) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    // TODO: check if there is a validate basic.

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

    // check if packet timestamp timeouted on the receiving chain
    // let consensus_state = ctx.channel_client_consensus_state(&(packet.source_port.clone(),
    // packet.source_channel.clone()), latest_height).ok_or_else(|| Kind::MissingClientConsensusState)?;

    //     let latest_timestamp =  consensus_state.latest_timestamp();

    //     let host_consensus_state = ctx.channel_host_consensus_state().ok_or_else(|| Kind::MissingHostConsensusState)?;
    //     let mut packet_timestamp = host_consensus_state.latest_timestamp();
    //     packet_timestamp = <Time as Add<Duration>>::add(packet_timestamp, Duration::from_nanos(packet.timeout_timestamp));

    //     if !packet.timeout_timestamp == 0 &&
    //     packet_timestamp.cmp(&latest_timestamp).eq(&Ordering::Less)
    //    {
    //    return Err(Kind::LowPacketTimestamp(latest_timestamp, packet_timestamp).into());
    //    }

    // check sequence number
    let next_seq_send = ctx
        .get_next_sequence_send(&(packet.source_port.clone(), packet.source_channel.clone()))
        .ok_or_else(|| Kind::MissingNextSendSeq)?;

    if packet.sequence.eq(&Sequence::from(*next_seq_send)) {
        return Err(
            Kind::InvalidPacketSequence(packet.sequence, Sequence::from(*next_seq_send)).into(),
        );
    }

    //let commitment = hash(packet.data,packet.timeout_height,packet.timeout_timestamp);

    output.log("success: packet send ");

    let result = PacketResult {
        send_seq_number: next_seq_send + 1,
        //commitment,
    };

    // let event_attributes = Attributes {
    //     // SendPacket {
    //     //     height: Default::default(),
    //     //     packet,
    //     // },
    //      ..Default::default()
    // };

    let height = <Height as TryFrom<u64>>::try_from(packet_height.revision_height).unwrap();

    output.emit(IBCEvent::SendPacketChannel(SendPacket { height, packet }));

    Ok(output.with_result(result))
}


#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::{events::IBCEvent, ics04_channel::packet::Packet};
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::version::get_compatible_versions;
    use crate::ics04_channel::channel::State;
    use crate::ics04_channel::packet::PacketResult;
    use crate::ics04_channel::msgs::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init;
    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use crate::ics04_channel::msgs::ChannelMsg;
    use crate::ics24_host::identifier::ConnectionId;
    use crate::mock::context::MockContext;

    #[test]
    fn send_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            packet: Packet,
            want_pass: bool,
        }

        let msg_chan_init =
            MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init()).unwrap();

        let context = MockContext::default();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();

        let init_conn_end = ConnectionEnd::new(
            ConnectionState::Init,
            msg_conn_init.client_id().clone(),
            msg_conn_init.counterparty().clone(),
            get_compatible_versions(),
            msg_conn_init.delay_period,
        );

        let ccid = <ConnectionId as FromStr>::from_str("defaultConnection-0");
        let cid = match ccid {
            Ok(v) => v,
            Err(_e) => ConnectionId::default(),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no connection exists in the context".to_string(),
                ctx: context.clone(),
                packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Processing fails because port does not have a capability associated"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(cid.clone(), init_conn_end.clone()),
                    packet: packet.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .with_connection(cid, init_conn_end)
                    .with_port_capability(
                        MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init())
                            .unwrap()
                            .port_id()
                            .clone(),
                    ),
                packet: packet,
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = send_packet(&test.ctx, test.packet);
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

                    // The object in the output is a ChannelEnd, should have init state.
                    let res: PacketResult = proto_output.result;
                    assert_eq!(res.channel_end.state().clone(), State::Init);
                    let msg_init = test.msg.clone();

                    if let ChannelMsg::ChannelOpenInit(msg_init) = msg_init {
                        assert_eq!(res.port_id.clone(), msg_init.port_id().clone());
                    }

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IBCEvent::OpenInitChannel(_)));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "send_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}