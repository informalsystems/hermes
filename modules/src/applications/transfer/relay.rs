//! This module implements the processing logic for ICS20 (token transfer) message.
use crate::applications::transfer::context::Ics20Context;
use crate::applications::transfer::error::Error as Ics20Error;
use crate::applications::transfer::packet::PacketData;
use crate::applications::transfer::{IbcCoin, Source, TracePrefix};
use crate::core::ics04_channel::packet::Packet;
use crate::prelude::*;

pub mod on_ack_packet;
pub mod on_recv_packet;
pub mod on_timeout_packet;
pub mod send_transfer;

fn refund_packet_token(
    ctx: &mut impl Ics20Context,
    packet: &Packet,
    data: &PacketData,
) -> Result<(), Ics20Error> {
    let sender = data
        .sender
        .clone()
        .try_into()
        .map_err(|_| Ics20Error::parse_account_failure())?;
    let amount: IbcCoin = data.token.clone().into();

    let prefix = TracePrefix::new(packet.source_port.clone(), packet.source_channel);
    match data.token.denom.source_chain(&prefix) {
        Source::Sender => {
            // unescrow tokens back to sender
            let escrow_address =
                ctx.get_channel_escrow_address(&packet.source_port, packet.source_channel)?;

            ctx.send_coins(&escrow_address, &sender, &amount)
        }
        // mint vouchers back to sender
        Source::Receiver => ctx.mint_coins(&sender, &amount),
    }
}
