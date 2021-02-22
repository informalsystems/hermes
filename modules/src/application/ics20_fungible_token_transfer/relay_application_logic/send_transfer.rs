use crate::application::ics20_fungible_token_transfer::error::{Error, Kind};
use crate::application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use crate::handler::HandlerOutput;
use crate::ics04_channel::packet::{Packet, Sequence};
use crate::ics04_channel::packet_handler::send_packet::send_packet;
use crate::ics04_channel::packet_handler::PacketResult;
use crate::ics26_routing::context::Ics26Context;

pub(crate) fn send_transfer<Ctx>(
    ctx: &Ctx,
    msg: MsgTransfer,
) -> Result<HandlerOutput<PacketResult>, Error>
where
    Ctx: Ics26Context,
{
    let source_channel_end = ctx
        .channel_end(&(msg.source_port.clone(), msg.source_channel.clone()))
        .ok_or_else(|| {
            Kind::ChannelNotFound(msg.source_port.clone(), msg.source_channel.clone())
        })?;

    let destination_port = source_channel_end.counterparty().port_id().clone();
    let destination_channel = source_channel_end.counterparty().channel_id();

    if destination_channel.is_none() {
        return Err(
            Kind::DestinationChannelNotFound(msg.source_port.clone(), msg.source_channel).into(),
        );
    }

    // get the next sequence
    let sequence = ctx
        .get_next_sequence_send(&(msg.source_port.clone(), msg.source_channel.clone()))
        .ok_or_else(|| {
            Kind::SequenceSendNotFound(msg.source_port.clone(), msg.source_channel.clone())
        })?;

    // begin createOutgoingPacket logic
    let _channel_cap = ctx
        .lookup_module_by_port(&msg.source_port.clone())
        .ok_or_else(|| Kind::ChannelCapabilityNotFound)?;

    //TODO: Application LOGIC.

    let packet = Packet {
        sequence: <Sequence as From<u64>>::from(*sequence),
        source_port: msg.source_port,
        source_channel: msg.source_channel,
        destination_port,
        destination_channel: destination_channel.unwrap().clone(),
        data: vec![],
        timeout_height: msg.timeout_height,
        timeout_timestamp: msg.timeout_timestamp,
    };

    let handler_output =
        send_packet(ctx, packet).map_err(|e| Kind::HandlerRaisedError.context(e))?;
    //TODO:  add event/atributes and writes to the store issued by the application logic for packet sending.
    Ok(handler_output)
}
