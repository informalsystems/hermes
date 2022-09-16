//! Message definitions for all ICS4 domain types: channel open & close handshake datagrams, as well
//! as packets.

use crate::core::{
	ics04_channel::{
		error::Error,
		msgs::{
			acknowledgement::MsgAcknowledgement, chan_close_confirm::MsgChannelCloseConfirm,
			chan_close_init::MsgChannelCloseInit, chan_open_ack::MsgChannelOpenAck,
			chan_open_confirm::MsgChannelOpenConfirm, chan_open_init::MsgChannelOpenInit,
			chan_open_try::MsgChannelOpenTry, recv_packet::MsgRecvPacket, timeout::MsgTimeout,
			timeout_on_close::MsgTimeoutOnClose,
		},
	},
	ics26_routing::context::{Ics26Context, ModuleId},
};

// Opening handshake messages.
pub mod chan_open_ack;
pub mod chan_open_confirm;
pub mod chan_open_init;
pub mod chan_open_try;

// Closing handshake messages.
pub mod chan_close_confirm;
pub mod chan_close_init;

// Packet specific messages.
pub mod acknowledgement;
pub mod recv_packet;
pub mod timeout;
pub mod timeout_on_close;

/// Enumeration of all possible messages that the ICS4 protocol processes.
#[derive(Clone, Debug, PartialEq)]
pub enum ChannelMsg {
	ChannelOpenInit(MsgChannelOpenInit),
	ChannelOpenTry(MsgChannelOpenTry),
	ChannelOpenAck(MsgChannelOpenAck),
	ChannelOpenConfirm(MsgChannelOpenConfirm),
	ChannelCloseInit(MsgChannelCloseInit),
	ChannelCloseConfirm(MsgChannelCloseConfirm),
}

impl ChannelMsg {
	pub(super) fn lookup_module(&self, ctx: &impl Ics26Context) -> Result<ModuleId, Error> {
		let module_id = match self {
			ChannelMsg::ChannelOpenInit(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
			ChannelMsg::ChannelOpenTry(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
			ChannelMsg::ChannelOpenAck(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
			ChannelMsg::ChannelOpenConfirm(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
			ChannelMsg::ChannelCloseInit(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
			ChannelMsg::ChannelCloseConfirm(msg) =>
				ctx.lookup_module_by_port(&msg.port_id).map_err(Error::ics05_port)?,
		};
		Ok(module_id)
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum PacketMsg {
	RecvPacket(MsgRecvPacket),
	AckPacket(MsgAcknowledgement),
	ToPacket(MsgTimeout),
	ToClosePacket(MsgTimeoutOnClose),
}
