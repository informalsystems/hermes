//! This module implements the processing logic for ICS20 (token transfer) message.
use crate::applications::ics20_fungible_token_transfer::context::Ics20Context;
use crate::applications::ics20_fungible_token_transfer::error::Error as Ics20Error;
use crate::applications::ics20_fungible_token_transfer::packet::PacketData;
use crate::applications::ics20_fungible_token_transfer::{IbcCoin, Source, TracePrefix};
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
    let sender = data.sender.to_string().parse()?;
    let amount: IbcCoin = data.token.clone().into();

    let prefix = TracePrefix::new(packet.source_port.clone(), packet.source_channel);
    match data.token.denom.source_chain(&prefix) {
        Source::Sender => {
            // unescrow tokens back to sender
            let escrow_address =
                ctx.get_channel_escrow_address(&packet.source_port, packet.source_channel)?;

            ctx.send_coins(&escrow_address, &sender, &amount)
        }
        Source::Receiver => {
            // mint vouchers back to sender
            ctx.mint_coins(&ctx.get_transfer_account(), &amount)?;
            ctx.send_coins_from_module_to_account(&ctx.get_transfer_account(), &sender, &amount).expect("unable to send coins from module to account despite previously minting coins to module account");
            Ok(())
        }
    }
}
