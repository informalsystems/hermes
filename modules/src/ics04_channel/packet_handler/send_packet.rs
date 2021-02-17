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
