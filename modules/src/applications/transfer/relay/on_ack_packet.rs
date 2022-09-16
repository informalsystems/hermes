use crate::{
	applications::transfer::{
		acknowledgement::Acknowledgement, context::Ics20Context, error::Error as Ics20Error,
		packet::PacketData, relay::refund_packet_token,
	},
	core::ics04_channel::packet::Packet,
};

pub fn process_ack_packet(
	ctx: &mut impl Ics20Context,
	packet: &Packet,
	data: &PacketData,
	ack: &Acknowledgement,
) -> Result<(), Ics20Error> {
	if matches!(ack, Acknowledgement::Error(_)) {
		refund_packet_token(ctx, packet, data)?;
	}

	Ok(())
}
