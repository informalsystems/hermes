//! This module implements the processing logic for ICS4 (channel) messages.

use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::msgs::ChannelMsg;
use crate::core::ics04_channel::{msgs::PacketMsg, packet::PacketResult};
use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::handler::HandlerOutput;

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

/// General entry point for processing any type of message related to the ICS4 channel open and
/// channel close handshake protocols.
pub fn channel_dispatch<Ctx>(
    ctx: &Ctx,
    msg: ChannelMsg,
) -> Result<HandlerOutput<ChannelResult>, Error>
where
    Ctx: ChannelReader,
{
    match msg {
        ChannelMsg::ChannelOpenInit(msg) => chan_open_init::process(ctx, msg),
        ChannelMsg::ChannelOpenTry(msg) => chan_open_try::process(ctx, msg),
        ChannelMsg::ChannelOpenAck(msg) => chan_open_ack::process(ctx, msg),
        ChannelMsg::ChannelOpenConfirm(msg) => chan_open_confirm::process(ctx, msg),
        ChannelMsg::ChannelCloseInit(msg) => chan_close_init::process(ctx, msg),
        ChannelMsg::ChannelCloseConfirm(msg) => chan_close_confirm::process(ctx, msg),
    }
}

/// Dispatcher for processing any type of message related to the ICS4 packet protocols.
pub fn packet_dispatch<Ctx>(ctx: &Ctx, msg: PacketMsg) -> Result<HandlerOutput<PacketResult>, Error>
where
    Ctx: ChannelReader,
{
    match msg {
        PacketMsg::RecvPacket(msg) => recv_packet::process(ctx, msg),
        PacketMsg::AckPacket(msg) => acknowledgement::process(ctx, msg),
        PacketMsg::ToPacket(msg) => timeout::process(ctx, msg),
        PacketMsg::ToClosePacket(msg) => timeout_on_close::process(ctx, msg),
    }
}
