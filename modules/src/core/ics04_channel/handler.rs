//! This module implements the processing logic for ICS4 (channel) messages.

use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::msgs::ChannelMsg;
use crate::core::ics04_channel::{msgs::PacketMsg, packet::PacketResult};
use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::core::ics26_routing::context::{
    Ics26Context, ModuleId, ModuleOutput, OnRecvPacketAck, Router,
};
use crate::handler::{HandlerOutput, HandlerOutputBuilder};

pub mod acknowledgement;
pub mod chan_close_confirm;
pub mod chan_close_init;
pub mod chan_open_ack;
pub mod chan_open_confirm;
pub mod chan_open_init;
pub mod chan_open_try;
pub mod recv_packet;
pub mod send_packet;
pub mod timeout;
pub mod timeout_on_close;
pub mod verify;
pub mod write_acknowledgement;

/// Defines the possible states of a channel identifier in a `ChannelResult`.
#[derive(Clone, Debug)]
pub enum ChannelIdState {
    /// Specifies that the channel handshake handler allocated a new channel identifier. This
    /// happens during the processing of either the `MsgChannelOpenInit` or `MsgChannelOpenTry`.
    Generated,

    /// Specifies that the handler reused a previously-allocated channel identifier.
    Reused,
}

#[derive(Clone, Debug)]
pub struct ChannelResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub channel_id_state: ChannelIdState,
    pub channel_cap: Capability,
    pub channel_end: ChannelEnd,
}

pub struct DispatchResult<R> {
    pub module_id: ModuleId,
    pub output: HandlerOutputBuilder<()>,
    pub result: R,
}

pub type ChannelDispatchResult = DispatchResult<ChannelResult>;
pub type PacketDispatchResult = DispatchResult<PacketResult>;

fn validate_route<Ctx: Ics26Context>(ctx: &Ctx, module_id: ModuleId) -> Result<ModuleId, Error> {
    ctx.router()
        .has_route(&module_id)
        .then(|| module_id)
        .ok_or_else(Error::route_not_found)
}

/// General entry point for processing any type of message related to the ICS4 channel open and
/// channel close handshake protocols.
pub fn channel_dispatch<Ctx>(ctx: &Ctx, msg: &ChannelMsg) -> Result<ChannelDispatchResult, Error>
where
    Ctx: Ics26Context,
{
    let (module_id, output) = match msg {
        ChannelMsg::ChannelOpenInit(msg) => ctx
            .lookup_module_by_port(msg.port_id.clone())
            .map_err(|_| Error::no_port_capability(msg.port_id.clone()))
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_open_init::process(ctx, msg, cap)?))),
        ChannelMsg::ChannelOpenTry(msg) => ctx
            .lookup_module_by_port(msg.port_id.clone())
            .map_err(|_| Error::no_port_capability(msg.port_id.clone()))
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_open_try::process(ctx, msg, cap)?))),
        ChannelMsg::ChannelOpenAck(msg) => ctx
            .lookup_module_by_channel(msg.channel_id, msg.port_id.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_open_ack::process(ctx, msg, cap)?))),
        ChannelMsg::ChannelOpenConfirm(msg) => ctx
            .lookup_module_by_channel(msg.channel_id, msg.port_id.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_open_confirm::process(ctx, msg, cap)?))),
        ChannelMsg::ChannelCloseInit(msg) => ctx
            .lookup_module_by_channel(msg.channel_id, msg.port_id.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_close_init::process(ctx, msg, cap)?))),
        ChannelMsg::ChannelCloseConfirm(msg) => ctx
            .lookup_module_by_channel(msg.channel_id, msg.port_id.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, chan_close_confirm::process(ctx, msg, cap)?))),
    }?;

    let HandlerOutput {
        result,
        log,
        events,
    } = output;
    let output = HandlerOutput::builder().with_log(log).with_events(events);
    Ok(ChannelDispatchResult {
        module_id,
        output,
        result,
    })
}

pub fn channel_callback<Ctx>(
    ctx: &mut Ctx,
    module_id: &ModuleId,
    msg: &ChannelMsg,
    mut result: ChannelResult,
    module_output: &mut ModuleOutput,
) -> Result<ChannelResult, Error>
where
    Ctx: Ics26Context,
{
    let cb = ctx
        .router_mut()
        .get_route_mut(module_id)
        .ok_or_else(Error::route_not_found)?;

    match msg {
        ChannelMsg::ChannelOpenInit(msg) => cb.on_chan_open_init(
            module_output,
            msg.channel.ordering,
            &msg.channel.connection_hops,
            &msg.port_id,
            &result.channel_id,
            &result.channel_cap,
            msg.channel.counterparty(),
            &msg.channel.version,
        )?,
        ChannelMsg::ChannelOpenTry(msg) => {
            let version = cb.on_chan_open_try(
                module_output,
                msg.channel.ordering,
                &msg.channel.connection_hops,
                &msg.port_id,
                &result.channel_id,
                &result.channel_cap,
                msg.channel.counterparty(),
                &msg.counterparty_version,
            )?;
            result.channel_end.version = version;
        }
        ChannelMsg::ChannelOpenAck(msg) => cb.on_chan_open_ack(
            module_output,
            &msg.port_id,
            &result.channel_id,
            &msg.counterparty_version,
        )?,
        ChannelMsg::ChannelOpenConfirm(msg) => {
            cb.on_chan_open_confirm(module_output, &msg.port_id, &result.channel_id)?
        }
        ChannelMsg::ChannelCloseInit(msg) => {
            cb.on_chan_close_init(module_output, &msg.port_id, &result.channel_id)?
        }
        ChannelMsg::ChannelCloseConfirm(msg) => {
            cb.on_chan_close_confirm(module_output, &msg.port_id, &result.channel_id)?
        }
    }
    Ok(result)
}

/// Dispatcher for processing any type of message related to the ICS4 packet protocols.
pub fn packet_dispatch<Ctx>(ctx: &Ctx, msg: &PacketMsg) -> Result<PacketDispatchResult, Error>
where
    Ctx: Ics26Context,
{
    let (module_id, output) = match msg {
        PacketMsg::RecvPacket(msg) => ctx
            .lookup_module_by_channel(
                msg.packet.destination_channel,
                msg.packet.destination_port.clone(),
            )
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, recv_packet::process(ctx, msg, cap)?))),
        PacketMsg::AckPacket(msg) => ctx
            .lookup_module_by_channel(msg.packet.source_channel, msg.packet.source_port.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, acknowledgement::process(ctx, msg, cap)?))),
        PacketMsg::ToPacket(msg) => ctx
            .lookup_module_by_channel(msg.packet.source_channel, msg.packet.source_port.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, timeout::process(ctx, msg, cap)?))),
        PacketMsg::ToClosePacket(msg) => ctx
            .lookup_module_by_channel(msg.packet.source_channel, msg.packet.source_port.clone())
            .and_then(|(mid, cap)| Ok((validate_route(ctx, mid)?, cap)))
            .and_then(|(mid, cap)| Ok((mid, timeout_on_close::process(ctx, msg, cap)?))),
    }?;
    let HandlerOutput {
        result,
        log,
        events,
    } = output;
    let output = HandlerOutput::builder().with_log(log).with_events(events);
    Ok(PacketDispatchResult {
        module_id,
        output,
        result,
    })
}

pub fn packet_callback<Ctx>(
    ctx: &mut Ctx,
    module_id: &ModuleId,
    msg: &PacketMsg,
    module_output: &mut ModuleOutput,
) -> Result<(), Error>
where
    Ctx: Ics26Context,
{
    let cb = ctx
        .router_mut()
        .get_route_mut(module_id)
        .ok_or_else(Error::route_not_found)?;

    match msg {
        PacketMsg::RecvPacket(msg) => {
            let result = cb.on_recv_packet(module_output, &msg.packet, &msg.signer);
            match result {
                OnRecvPacketAck::Nil(write_fn) | OnRecvPacketAck::Successful(_, write_fn) => {
                    write_fn(cb.as_any_mut());
                }
                OnRecvPacketAck::Failed(_) => {}
            }
        }
        PacketMsg::AckPacket(msg) => cb.on_acknowledgement_packet(
            module_output,
            &msg.packet,
            &msg.acknowledgement,
            &msg.signer,
        )?,
        PacketMsg::ToPacket(msg) => {
            cb.on_timeout_packet(module_output, &msg.packet, &msg.signer)?
        }
        PacketMsg::ToClosePacket(msg) => {
            cb.on_timeout_packet(module_output, &msg.packet, &msg.signer)?
        }
    };
    Ok(())
}
