use crate::{
	applications::transfer::{
		context::Ics20Context, error::Error as Ics20Error, packet::PacketData,
		relay::refund_packet_token,
	},
	core::ics04_channel::packet::Packet,
};

pub fn process_timeout_packet(
	ctx: &mut impl Ics20Context,
	packet: &Packet,
	data: &PacketData,
) -> Result<(), Ics20Error> {
	refund_packet_token(ctx, packet, data)
}
