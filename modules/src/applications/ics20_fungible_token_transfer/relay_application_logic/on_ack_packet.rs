use crate::applications::ics20_fungible_token_transfer::acknowledgement::Acknowledgement;
use crate::applications::ics20_fungible_token_transfer::context::Ics20Context;
use crate::applications::ics20_fungible_token_transfer::error::Error as Ics20Error;
use crate::applications::ics20_fungible_token_transfer::packet::PacketData;
use crate::applications::ics20_fungible_token_transfer::relay_application_logic::refund_packet_token;
use crate::core::ics04_channel::packet::Packet;

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
