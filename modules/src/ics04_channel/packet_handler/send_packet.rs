use std::cmp::Ordering;

use crate::{handler::{HandlerOutput, HandlerResult}, ics04_channel::packet::Sequence}; 
use crate::ics02_client::state::ClientState;
use crate::ics04_channel::channel::State;
use crate::ics04_channel::channel::Counterparty;
use crate::ics04_channel::{context::ChannelReader, error::Error, packet::Packet,error::Kind};
use crate::ics05_port::capabilities::Capability;
//use crate::Height;



use super::PacketResult;

pub fn send_packet(
    ctx: &dyn ChannelReader,
    capability: Capability,
     packet: Packet,
) -> HandlerResult<PacketResult, Error> {

    let mut output = HandlerOutput::builder();


    // TODO: check if there is a validate basic. 

    let source_channel_end = ctx.channel_end(&(
        packet.source_port.clone(), 
        packet.source_channel.clone()
    )).ok_or_else(||Kind::ChannelNotFound.context( packet.source_channel.clone().to_string()))?;
    
    if source_channel_end.state_matches(&State::Closed){
        return Err(Kind::ChannelClosed(packet.source_channel.clone()).into());
    }

    // TODO: Capability Checked in ICS20 as well. Check Difs. 
    let channel_cap = ctx.authenticated_capability(&packet.source_port.clone())?;
    
    let channel_id = match source_channel_end.counterparty().channel_id(){
        Some(c) => Some(c.clone()),
        None => None,
    };

    let counterparty =
    Counterparty::new(source_channel_end.counterparty().port_id().clone(), channel_id);
    
    if !source_channel_end.counterparty_matches(&counterparty) {
		return Err(Kind::InvalidPacketCounterparty(packet.source_port.clone(),packet.source_channel.clone()).into());
	}

    let connection_end = ctx
        .connection_end(&source_channel_end.connection_hops()[0])
        .ok_or_else(|| Kind::MissingConnection(source_channel_end.connection_hops()[0].clone()))?;


    let client_state = ctx.channel_client_state(&(packet.source_port.clone(), 
        packet.source_channel.clone())).ok_or_else(|| Kind::MissingClientState)?;
    
    
    // prevent accidental sends with clients that cannot be updated
    if client_state.is_frozen() {
            return Err(Kind::FrozenClient(connection_end.client_id().clone()).into());
        }
        
	// check if packet timeouted on the receiving chain

    let latest_height = client_state.latest_height(); 
    if !packet.timeout_height.is_zero() && 
        (latest_height.cmp(&packet.timeout_height.clone()).eq(&Ordering::Greater) 
        ||latest_height.cmp(&packet.timeout_height.clone()).eq(&Ordering::Equal))
       {
       return Err(Kind::LowPacketHeight(latest_height, packet.timeout_height.clone()).into());
       }


    let consensus_state = ctx.channel_client_consensus_state(&(packet.source_port.clone(), 
    packet.source_channel.clone()), latest_height).ok_or_else(|| Kind::MissingClientConsensusState)?;

    let latest_timestamp =  consensus_state.latest_timestamp(); 
    
    
//     if !packet.timeout_timestamp.is_zero() && 
//     (latest_timestamp.cmp(&packet.timeout_timestamp.clone()).eq(&Ordering::Greater) 
//     ||latest_timestamp.cmp(&packet.timeout_timestamp.clone()).eq(&Ordering::Equal))
//    {
//    return Err(Kind::LowPacketTimestamp(latest_timestamp, packet.timeout_timestamp.clone()).into());
//    }


    let next_seq_send = ctx.get_next_sequence_send(&(
        packet.source_port.clone(), 
        packet.source_channel.clone()
    )).ok_or_else(|| Kind::MissingNextSendSeq)?; 

    if <Sequence as From<Sequence>>::from(packet.sequence) != next_seq_send {
        return Err(Kind::InvalidPacketSequence(packet.sequence,next_seq_send).into());
    }
    
    output.log("success: packet send ");

    // let result = ClientResult::Create(Result {
    //     client_id: client_id.clone(),
    //     client_type: msg.client_state().client_type(),
    //     client_state: msg.client_state(),
    //     consensus_state: msg.consensus_state(),
    // });

    // let event_attributes = Attributes {
    //     client_id,
    //     ..Default::default()
    // };
    // output.emit(IBCEvent::CreateClient(event_attributes.into()));

    // Ok(output.with_result(result))

    Ok(output);

}